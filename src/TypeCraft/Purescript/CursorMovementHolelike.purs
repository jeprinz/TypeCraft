module TypeCraft.Purescript.CursorMovementHoles where

import Prelude
import Prim hiding (Type)

import Data.List (null)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.CursorMovement (getPath, stepCursorBackwards, stepCursorForwardsImpl)
import TypeCraft.Purescript.Grammar (TermBind(..), Type(..), TypeBind(..))
import TypeCraft.Purescript.State (CursorLocation(..))

isHolelike :: CursorLocation -> Boolean
-- yes, not even `Hole`, because you should jump _inside_ the hole (at
-- `InsideHoleCursor`) rather than to the term `Hole`
isHolelike (TermCursor _ _ _ _) = false

isHolelike (TypeCursor _ _ (THole _ _ _ _)) = true

isHolelike (TypeCursor _ _ _) = false

isHolelike (TypeBindCursor _ _ (TypeBind md _)) = md.varName == ""

isHolelike (TermBindCursor _ _ (TermBind md _)) = md.varName == ""

isHolelike (CtrListCursor _ _ _) = false -- !TODO debatable

isHolelike (CtrParamListCursor _ _ _) = false -- !TODO debatable

isHolelike (TypeBindListCursor _ _ _) = false -- !TODO debatable

isHolelike (InsideHoleCursor _ _ _) = true

stepCursorNextHolelike :: CursorLocation -> CursorLocation
stepCursorNextHolelike cursor = case stepCursorForwardsImpl 0 cursor of
  Just cursor' ->
    if isHolelike cursor' then
      cursor'
    else
      stepCursorNextHolelike cursor'
  Nothing -> cursor

stepCursorPrevHolelike :: CursorLocation -> CursorLocation
stepCursorPrevHolelike cursor
  | null (getPath cursor) = cursor -- at top
  | otherwise =
    let
      cursor' = stepCursorBackwards cursor
    in
      if isHolelike cursor' then
        cursor'
      else
        stepCursorPrevHolelike cursor'
