module TypeCraft.Purescript.ModifyState where

import Prelude
import Data.Array ((:), uncons)
import Data.Array as Array
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.ChangePath (chTermPath, chTypePath)
import TypeCraft.Purescript.Context (ctxInject, kCtxInject)
import TypeCraft.Purescript.CursorMovement (moveSelectLeft, moveSelectRight, stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.Dentist (downPathToCtxChange)
import TypeCraft.Purescript.Grammar (Change(..), TermBind(..), Tooth(..), TypeBind(..), freshHole, freshTHole)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.MD (defaultTypeBoundaryMD)
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.ModifyIndentation (toggleIndentation)
import TypeCraft.Purescript.State (Clipboard(..), Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), SelectMode, State, botSelectOrientation, cursorLocationToSelect, emptyQuery, getCompletion, makeCursorMode, selectToCursorLocation, topSelectOrientation)
import TypeCraft.Purescript.TypeChangeAlgebra (getAllEndpoints)
import TypeCraft.Purescript.Unification (applySubType, subTermPath)
import TypeCraft.Purescript.Util (hole')

handleKey :: Key -> State -> Maybe State
handleKey key st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TypeBindCursor ctxs path (TypeBind md tyVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TypeBindCursor ctxs path (TypeBind md { varName = varName } tyVarId) } }
    TermBindCursor ctxs path (TermBind md tmVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TermBindCursor ctxs path (TermBind md { varName = varName } tmVarId) } }
    CtrParamListCursor ctxs path ctrs -> hole' "handleKey CtrParamListCursor"
    _
      | Just query <- manipulateQuery key st cursorMode -> do
        -- not the we don't `checkpoint` here, since every little modification
        -- of the query string and selection shouldn't by undoable
        pure $ st { mode = CursorMode cursorMode { query = query } }
      | (key.ctrlKey || key.metaKey) && key.key == "z" -> undo st
      | (key.ctrlKey || key.metaKey) && key.key == "Z" -> redo st
      | key.key == "ArrowLeft" && key.shiftKey -> moveSelectPrev st
      | key.key == "ArrowRight" && key.shiftKey -> moveSelectNext st
      | key.key == "ArrowLeft" -> moveCursorPrev st
      | key.key == "ArrowRight" -> moveCursorNext st
      | key.key == "Escape" -> pure $ st { mode = CursorMode cursorMode { query = emptyQuery } }
      | key.key == "Tab" -> do
        cursorLocation' <- toggleIndentation cursorMode.cursorLocation
        pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
      | key.key == "Enter" -> do
        cursorMode' <- submitQuery cursorMode
        -- checkpoints the pre-submission mode with a cleared query string
        pure
          $ (checkpoint st { mode = CursorMode cursorMode { query { string = "" } } })
              { mode = CursorMode cursorMode' }
      | key.key == "Backspace" -> delete st
      | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
      | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
      | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
      | otherwise -> Nothing
  SelectMode selectMode
    | key.key == "Escape" -> pure $ st { mode = makeCursorMode (selectToCursorLocation selectMode.select) }
    | key.key == "ArrowLeft" && key.shiftKey -> moveSelectPrev st
    | key.key == "ArrowRight" && key.shiftKey -> moveSelectNext st
    | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
    | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
    | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
    | otherwise -> Nothing

submitQuery :: CursorMode -> Maybe CursorMode
submitQuery cursorMode = case cursorMode.cursorLocation of
  TermCursor ctxs ty path tm ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionTerm tm' {-ty'-} sub ->
            let
              ty' = applySubType sub ty
            in
              let
                path' = subTermPath sub path
              in
                pure
                  -- TODO: note from Jacob: always having Replace here doesn't seem right to me. Shouldn't terms only be filled in when they are the exact type (modulo unification) in the first place?
                  -- As opposed to path completions, where you do have typechanges.
                  { cursorLocation: TermCursor ctxs ty' path' tm'
                  , query: emptyQuery
                  }
          CompletionTermPath pathNew ch ->
            let
              path' = chTermPath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
            in
              let
                chCtxs = downPathToCtxChange ctxs (List.reverse pathNew)
              in
                let
                  newCtxs = snd (getAllEndpoints chCtxs)
                in
                  pure
                    { cursorLocation: TermCursor newCtxs ty (pathNew <> path') tm
                    , query: emptyQuery
                    }
          _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionType ty' ->
            let
              path' = chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) (Replace ty ty') path
            in
              pure
                { cursorLocation: TypeCursor ctxs path' ty'
                , query: emptyQuery
                }
          CompletionTypePath pathNew ch ->
            let
              path' = chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
            in
              pure
                { cursorLocation: TypeCursor ctxs (pathNew <> path') ty
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionType* completion at a TypeCursor"
  _ -> Nothing -- TODO: submit queries at other kinds of cursors?

checkpoint :: State -> State
checkpoint st = st { history = st.mode : st.history }

setCursor :: CursorLocation -> State -> Maybe State
setCursor cursorLocation st = pure $ st { mode = makeCursorMode cursorLocation }

-- doesn't `checkpoint`
moveCursorPrev :: State -> Maybe State
moveCursorPrev st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorBackwards cursorLocation) }
  _ -> Nothing -- TODO: escape select

-- doesn't `checkpoint`
moveCursorNext :: State -> Maybe State
moveCursorNext st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorForwards cursorLocation) }
  _ -> Nothing -- TODO: escape select

moveSelectPrev :: State -> Maybe State
moveSelectPrev st = do
  select <- case st.mode of
    CursorMode { cursorLocation } -> pure $ cursorLocationToSelect botSelectOrientation cursorLocation
    SelectMode { select } -> pure select
  mode <- moveSelectLeft select
  pure $ st { mode = mode }

moveSelectNext :: State -> Maybe State
moveSelectNext st = do
  select <- case st.mode of
    CursorMode { cursorLocation } -> pure $ cursorLocationToSelect topSelectOrientation cursorLocation
    SelectMode { select } -> pure select
  mode <- moveSelectRight select
  pure $ st { mode = mode }

setSelect :: Select -> State -> Maybe State
setSelect select st = pure $ st { mode = SelectMode { select } }

requireCursorMode :: State -> Maybe CursorMode
requireCursorMode st = case st.mode of
  CursorMode cursorMode -> pure cursorMode
  _ -> Nothing

undo :: State -> Maybe State
undo st = do
  { head, tail } <- uncons st.history
  if Array.length st.history > 1 then
    pure $ st { mode = head, history = tail, future = st.mode : st.future }
  else
    pure $ st { mode = head }

redo :: State -> Maybe State
redo st = do
  { head, tail } <- uncons st.future
  pure $ st { mode = head, history = st.mode : st.history, future = tail }

cut :: State -> Maybe State
cut st = do
  traceM "cut"
  clip <- modeToClipboard st.mode
  st <- delete st
  pure $ st { clipboard = clip }

copy :: State -> Maybe State
copy st = do
  traceM "redo"
  clip <- modeToClipboard st.mode
  pure $ st { clipboard = clip }

modeToClipboard :: Mode -> Maybe Clipboard
modeToClipboard = case _ of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TermCursor ctxs ty tmPath tm -> pure $ TermClip ctxs ty tm
    _ -> hole' "modeToClipboard"
  SelectMode selectMode -> case selectMode.select of
    TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori -> Just $ TermPathClip ctxs1 ty1 tmPath2 ctxs2 ty2
    _ -> hole' "modeToClipboard"

-- TODO: properly use contexts and freshen variables
paste :: State -> Maybe State
paste st = do
  traceM "paste"
  case st.clipboard of
    EmptyClip -> Nothing
    TermClip ctxs' ty' tm' -> case st.mode of
      CursorMode cursorMode -> case cursorMode.cursorLocation of
        TermCursor ctxs ty tmPath tm -> pure $ st { mode = makeCursorMode $ TermCursor ctxs ty (TypeBoundary1 defaultTypeBoundaryMD (Replace ty' ty) List.: tmPath) tm' }
        _ -> Nothing
      SelectMode selectMode -> Nothing
    TermPathClip ctxs1' ty1' tmPath' ctxs2' ty2' -> case st.mode of
      CursorMode cursorMode -> case cursorMode.cursorLocation of
        TermCursor ctxs ty tmPath tm ->
          pure
            $ st
                { mode =
                  makeCursorMode
                    $ TermCursor ctxs ty
                        ( (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty ty2'))
                            <> tmPath'
                            <> (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty1' ty))
                            <> tmPath
                        )
                        tm
                }
        _ -> Nothing
      SelectMode selectMode -> case selectMode.select of
        TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori ->
          pure
            $ st
                { mode =
                  makeCursorMode
                    $ TermCursor ctxs1 ty1
                        ( (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty2 ty2'))
                            <> tmPath2
                            <> (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty1' ty1))
                            <> tmPath1
                        )
                        tm2
                }
        _ -> Nothing
    _ -> hole' "TODO: do other syntactic cases for paste"

delete :: State -> Maybe State
delete st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TermCursor ctxs ty path _tm -> do
      let
        cursorLocation' = TermCursor ctxs ty path (freshHole unit)
      pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
    TypeCursor ctxs path ty -> do
      let
        ty' = (freshTHole unit)

        cursorLocation' = TypeCursor ctxs (chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) (Replace ty' ty) path) ty'
      pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
    _ -> hole' "delete: other syntactical kids of cursors"
  SelectMode selectMode -> case selectMode.select of
    TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori -> pure $ st { mode = makeCursorMode $ TermCursor ctxs1 ty1 ((TypeBoundary1 defaultTypeBoundaryMD (Replace ty2 ty1)) List.: tmPath1) tm2 }
    _ -> hole' "delete: other syntactical kinds of selects"

escape :: State -> Maybe State
escape = hole' "escape"
