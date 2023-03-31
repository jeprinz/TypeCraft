module TypeCraft.Purescript.CursorMovementHoles where

import Prelude
import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec
import Data.Array as Array
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:), find, last, init, null, head, index, length)
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe)
import Data.Maybe (maybe)
import Data.Ord (abs)
import Data.Tuple.Nested (type (/\), (/\))
import Debug (trace)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Util (fromJust, hole')
import TypeCraft.Purescript.Util (head')

-- A ""

moveCursorNextHole :: State -> Maybe State
moveCursorNextHole = unsafeThrow "moveCursorNextHole"

goRightUntilHole :: CursorLocation -> Maybe CursorLocation
goRightUntilHole = unsafeThrow "goRightUntilHole"
