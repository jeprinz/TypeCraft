module TypeCraft.Purescript.ModifyState where

import Prelude
import Data.Array ((:))
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.CursorMovement (stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.State (CursorLocation, Mode(..), Select, State, emptyQuery, makeCursorMode)
import TypeCraft.Purescript.Util (hole')

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
