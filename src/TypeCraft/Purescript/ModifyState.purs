module TypeCraft.Purescript.ModifyState where

import Prelude
import Data.Array ((:), uncons)
import Data.Array as Array
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.ChangePath
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.CursorMovement
import TypeCraft.Purescript.Dentist
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.MD (defaultTypeBoundaryMD)
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.ModifyIndentation (toggleIndentation)
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.Unification
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Alpha
import Debug (trace)
import Data.Tuple.Nested

handleKey :: Key -> State -> Maybe State
handleKey key st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TypeBindCursor ctxs path (TypeBind md tyVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TypeBindCursor ctxs path (TypeBind md { varName = varName } tyVarId) } }
    TermBindCursor ctxs path (TermBind md tmVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TermBindCursor ctxs path (TermBind md { varName = varName } tmVarId) } }
    --    CtrParamListCursor ctxs path ctrs -> hole' "handleKey CtrParamListCursor" -- Jacob Note: why was this line here? I'm not sure.
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
      | key.key == "Escape" -> escape st
      | key.key == "Tab" -> do
        cursorLocation' <- toggleIndentation cursorMode.cursorLocation
        pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
      | key.key == "Enter" -> submitQuery st
      | key.key == "Backspace" -> delete st
      | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
      | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
      | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
      | otherwise -> Nothing
  SelectMode selectMode
    | key.key == "Escape" -> escape st
    | key.key == "ArrowLeft" && key.shiftKey -> moveSelectPrev st
    | key.key == "ArrowRight" && key.shiftKey -> moveSelectNext st
    | key.key == "ArrowLeft" -> moveCursorPrev st
    | key.key == "ArrowRight" -> moveCursorNext st
    | key.key == "Backspace" -> delete st
    | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
    | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
    | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
    | otherwise -> Nothing

submitQuery :: State -> Maybe State
submitQuery st = case st.mode of
  CursorMode cursorMode -> do
    cursorMode' <- submitQuery' cursorMode
    -- checkpoints the pre-submission mode with a cleared query string
    pure
      $ (checkpoint st { mode = CursorMode cursorMode { query { string = "" } } })
          { mode = CursorMode cursorMode' }
  _ -> Nothing

modifyQuery :: (Query -> Query) -> State -> Maybe State
modifyQuery f st = case st.mode of
  CursorMode cursorMode -> pure st { mode = CursorMode cursorMode { query = f cursorMode.query } }
  _ -> Nothing

submitQuery' :: CursorMode -> Maybe CursorMode
submitQuery' cursorMode = case cursorMode.cursorLocation of
  TermCursor ctxs ty path tm ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionTerm tm' {-ty'-} sub ->
            let
              ty' = applySubType sub ty

              path' = subTermPath sub path

              ctxs' = subAllCtx sub ctxs
            in
              pure
                { cursorLocation: TermCursor ctxs' ty' path' tm'
                , query: emptyQuery
                }
          CompletionTermPath pathNew ch move ->
            let
              (kctx' /\ ctx') /\ path' = chTermPath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
              ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
              chCtxs = downPathToCtxChange ctxs' (List.reverse pathNew)
              tm' = chTermCtxOnly kctx' ctx' ty tm
              newCtxs = snd (getAllEndpoints chCtxs)
            in
              pure
                { cursorLocation: move $ TermCursor newCtxs ty (pathNew <> path') tm'
                , query: emptyQuery
                }
          CompletionTermPath2 _ newState ->
              pure
                { cursorLocation: newState unit
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionType ty' sub ->
--            let path' = subTypePath sub path in
--            let ctxs' = subAllCtx sub ctxs in
            let (kctx' /\ ctx') /\ path' = chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) (Replace ty ty') path in
            let ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') } in
              pure
                  { cursorLocation: TypeCursor ctxs' path' ty'
                  , query: emptyQuery
                  }
          CompletionTypePath pathNew ch ->
            let (kctx' /\ ctx') /\ path' = chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path in
            let ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') } in
                pure
                  { cursorLocation: TypeCursor ctxs' (pathNew <> path') ty
                  , query: emptyQuery
                  }
          _ -> unsafeThrow "tried to submit a non-CompletionType* completion at a TypeCursor"
  CtrListCursor ctxs path ctrs ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionCtrListPath pathNew ch ->
            let
              path' = chListCtrPath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
            in
              pure
                { cursorLocation: CtrListCursor ctxs (pathNew <> path') ctrs
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  CtrParamListCursor ctxs path ctrParams ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionCtrParamListPath pathNew ch ->
            let
              path' = chListCtrParamPath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
            in
              pure
                { cursorLocation: CtrParamListCursor ctxs (pathNew <> path') ctrParams
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  TypeBindListCursor ctxs path tyBinds ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionTypeBindListPath pathNew ch ->
            let
              path' = chListTypeBindPath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) ch path
            in
              pure
                { cursorLocation: TypeBindListCursor ctxs (pathNew <> path') tyBinds
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  _ -> Nothing -- TODO: submit queries at other kinds of cursors?

checkpoint :: State -> State
checkpoint st = st { history = st.mode : st.history }

-- doesn't `checkpoint`
moveCursorPrev :: State -> Maybe State
moveCursorPrev st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorBackwards cursorLocation) }
  _ -> do moveCursorPrev =<< escape st

-- doesn't `checkpoint`
moveCursorNext :: State -> Maybe State
moveCursorNext st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorForwards cursorLocation) }
  _ -> moveCursorNext =<< escape st

moveSelectPrev :: State -> Maybe State
moveSelectPrev st = do
  select <- case st.mode of
    CursorMode { cursorLocation } -> cursorLocationToSelect botSelectOrientation cursorLocation
    SelectMode { select } -> pure select
  mode <- moveSelectLeft select
  pure $ st { mode = mode }

moveSelectNext :: State -> Maybe State
moveSelectNext st = do
  select <- case st.mode of
    CursorMode { cursorLocation } ->
      if (List.null (getCursorChildren cursorLocation)) then
        Nothing
      else
        cursorLocationToSelect topSelectOrientation cursorLocation
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
  traceM "copy"
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
delete st =
  trace "delete" \_ -> case st.mode of
    CursorMode cursorMode -> case cursorMode.cursorLocation of
      TermCursor ctxs ty path _tm -> do
        let
          cursorLocation' = TermCursor ctxs ty path (freshHole unit)
        pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
      TypeCursor ctxs path ty -> do
        let
          ty' = (freshTHole unit)

          (kctx' /\ ctx') /\ path' = (chTypePath (kCtxInject ctxs.kctx ctxs.actx) (ctxInject ctxs.ctx) (Replace ty ty') path)

          ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }

          cursorLocation' = TypeCursor ctxs' path' ty'
        pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
      _ -> hole' "delete: other syntactical kids of cursors"
    SelectMode selectMode -> case selectMode.select of
      TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori ->
        let change = termPathToChange ty2 tmPath2 in
        let (kctx' /\ ctx') /\ tmPath1' = chTermPath (kCtxInject ctxs2.kctx ctxs2.actx) (ctxInject ctxs2.ctx) (invert change) tmPath1 in
        let ctxs' = ctxs2 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') } in
        pure $ st {mode = makeCursorMode $ TermCursor ctxs' ty2 tmPath1' tm2}
      TypeSelect topPath ctxs1 ty1 middlePath ctxs2 ty2 ori ->
        let change = typePathToChange ty2 middlePath in
--chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> CAllContext /\ UpPath
        let (kctx' /\ ctx') /\ topPath' = chTypePath (kCtxInject ctxs2.kctx ctxs2.actx) (ctxInject ctxs2.ctx) (invert change) topPath in
        let ctxs' = ctxs2 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') } in
        pure $ st {mode = makeCursorMode $ TypeCursor ctxs' topPath' ty2}
      TypeBindListSelect topPath ctxs1 tyBinds1 middlePath ctxs2 tyBinds2 ori ->
        let innerCh = chTypeBindList tyBinds2 in
        let change = typeBindPathToChange innerCh middlePath in
        let topPath' = chListTypeBindPath (kCtxInject ctxs2.kctx ctxs2.actx) (ctxInject ctxs2.ctx) (invertListTypeBindChange change) topPath in
        pure $ st {mode = makeCursorMode $ TypeBindListCursor ctxs2 topPath' tyBinds2}
      _ -> hole' "delete: other syntactical kinds of selects"

escape :: State -> Maybe State
escape st = case st.mode of
  CursorMode cursorMode -> do
    pure $ st { mode = CursorMode cursorMode { query = emptyQuery } }
  SelectMode selectMode -> do
    pure $ st { mode = makeCursorMode (selectToCursorLocation selectMode.select) }
