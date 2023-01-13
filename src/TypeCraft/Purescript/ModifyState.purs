module TypeCraft.Purescript.ModifyState where

import Prelude
import Data.Array ((:))
import Data.Maybe (Maybe(..))
import Debug (trace)
import TypeCraft.Purescript.CursorMovement (stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.Grammar (TermBind(..), TypeBind(..))
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.State (CursorLocation(..), CursorMode, Mode(..), Select, State, emptyQuery, makeCursorMode)
import TypeCraft.Purescript.Util (hole')

handleKey :: String -> State -> Maybe State
handleKey key st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TypeBindCursor ctxs path (TypeBind md tyVarId)
      | Just varName <- manipulateString key md.varName -> pure $ setMode (CursorMode cursorMode { cursorLocation = TypeBindCursor ctxs path (TypeBind md { varName = varName } tyVarId) }) st
    TermBindCursor ctxs path (TermBind md tmVarId)
      | Just varName <- manipulateString key md.varName -> pure $ setMode (CursorMode cursorMode { cursorLocation = TermBindCursor ctxs path (TermBind md { varName = varName } tmVarId) }) st
    CtrParamListCursor ctxs path ctrs -> hole' "handleKey CtrParamListCursor"
    _
      | Just query <- manipulateQuery key st cursorMode -> pure st { mode = CursorMode cursorMode { query = query } }
      | key == "ArrowLeft" -> moveCursorPrev st
      | key == "ArrowRight" -> moveCursorNext st
      | key == "Escape" -> pure st { mode = CursorMode cursorMode { query = emptyQuery } }
      | key == "Enter" -> pure st -- TODO
      | otherwise -> Nothing
  SelectMode selectMode -> hole' "handleKey: SelectMode"

-- caches old mode in history
setMode :: Mode -> State -> State
setMode mode st =
  st
    { mode = mode
    , history = st.mode : st.history
    }

setCursor :: CursorLocation -> State -> Maybe State
setCursor cursorLocation st =
  Just
    $ setMode (makeCursorMode cursorLocation) st

moveCursorPrev :: State -> Maybe State
moveCursorPrev st = case st.mode of
  CursorMode { cursorLocation } ->
    Just
      $ setMode (makeCursorMode (stepCursorBackwards cursorLocation)) st
  _ -> Nothing -- TODO: escape select

moveCursorNext :: State -> Maybe State
moveCursorNext st = case st.mode of
  CursorMode { cursorLocation } ->
    Just
      $ setMode (makeCursorMode (stepCursorForwards cursorLocation)) st
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
undo = hole' "undo"

redo :: State -> Maybe State
redo = hole' "redo"

cut :: State -> Maybe State
cut = hole' "cut"

copy :: State -> Maybe State
copy = hole' "copy"

paste :: State -> Maybe State
paste = hole' "paste"

delete :: State -> Maybe State
delete = hole' "delete"

escape :: State -> Maybe State
escape = hole' "escape"
