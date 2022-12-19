module TypeCraft.Purescript.ModifyState where

import Prelude
import TypeCraft.Purescript.State
import Data.Maybe (Maybe)
import TypeCraft.Purescript.Util (hole)

moveCursorPrev :: State -> Maybe State
moveCursorPrev = hole

moveCursorNext :: State -> Maybe State
moveCursorNext = hole

moveSelectPrev :: State -> Maybe State
moveSelectPrev = hole

moveSelectNext :: State -> Maybe State
moveSelectNext = hole

undo :: State -> Maybe State
undo = hole

redo :: State -> Maybe State
redo = hole

cut :: State -> Maybe State
cut = hole

copy :: State -> Maybe State
copy = hole

paste :: State -> Maybe State
paste = hole

delete :: State -> Maybe State
delete = hole

escape :: State -> Maybe State
escape = hole
