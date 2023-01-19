module TypeCraft.Purescript.ModifyState where

import Data.Tuple.Nested
import Prelude

import Data.Array ((:), uncons)
import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Debug (trace, traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.ChangePath (chTermPath, chTypePath)
import TypeCraft.Purescript.ChangeTerm (chType, chTypeParamList)
import TypeCraft.Purescript.Context (ctxInject, kCtxInject)
import TypeCraft.Purescript.Context (kCtxInject)
import TypeCraft.Purescript.CursorMovement (stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.Grammar (Change(..), TermBind(..), TypeBind(..), freshHole, freshTHole)
import TypeCraft.Purescript.Grammar (tyInject)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Query, Select, State, emptyQuery, getCompletion, isEmptyQuery, makeCursorMode)
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
      | key.key == "ArrowLeft" -> moveCursorPrev st
      | key.key == "ArrowRight" -> moveCursorNext st
      | key.key == "Escape" -> pure $ st { mode = CursorMode cursorMode { query = emptyQuery } }
      | key.key == "Enter" -> do
        cursorMode' <- submitQuery cursorMode
        -- checkpoints the pre-submission mode with a cleared query string
        pure
          $ (checkpoint st { mode = CursorMode cursorMode { query { string = "" } } })
              { mode = CursorMode cursorMode' }
      | key.key == "Backspace" -> delete st
      | otherwise -> Nothing
  SelectMode selectMode -> hole' "handleKey: SelectMode"

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
              path' = chTermPath (kCtxInject ctxs.kctx) (ctxInject ctxs.ctx) ch path
            in
              pure
                { cursorLocation: TermCursor ctxs ty (pathNew <> path') tm
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionType ty' ->
            let
              path' = chTypePath (kCtxInject ctxs.kctx) (ctxInject ctxs.ctx) (Replace ty ty') path
            in
              pure
                { cursorLocation: TypeCursor ctxs path' ty'
                , query: emptyQuery
                }
          CompletionTypePath pathNew ch ->
            let
              path' = chTypePath (kCtxInject ctxs.kctx) (ctxInject ctxs.ctx) ch path
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
moveSelectPrev = hole' "moveSelectPrev"

moveSelectNext :: State -> Maybe State
moveSelectNext = hole' "moveSelectNext"

setSelect :: Select -> State -> Maybe State
setSelect = hole' "setSelect"

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
cut = hole' "cut"

copy :: State -> Maybe State
copy = hole' "copy"

paste :: State -> Maybe State
paste = hole' "paste"

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
        cursorLocation' = TypeCursor ctxs (chTypePath Map.empty Map.empty (Replace ty ty') path) ty'
      pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
    _ -> Nothing
  _ -> Nothing

escape :: State -> Maybe State
escape = hole' "escape"
