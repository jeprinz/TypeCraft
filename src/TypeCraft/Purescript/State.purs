module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.TermRec (TermRecValue)
import TypeCraft.Purescript.TermRec (recTerm)
import TypeCraft.Purescript.TermRec (TypeRecValue)
import TypeCraft.Purescript.TermRec (recType)
import TypeCraft.Purescript.PathRec (recTermPath)
import TypeCraft.Purescript.PathRec (recTypePath)
import Data.Maybe (Maybe)
import Data.Maybe (Maybe(..))
import Data.List (length)
import Data.List (index)

{-
This file will contain possible states for the editor
-}

data Clipboard = EmptyClip -- add more later, not priority yet

data CodeState = CursorState CursorLocation
data CursorLocation = TermCursor TypeContext TermContext Type TermPath Term | TypeCursor TypeContext TermContext TypePath Type -- add more later, for now this is fine

getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor kctx ctx ty up term) =
    recTerm
        {
            lambda: \md x ty body -> TermCursor body.kctx body.ctx body.ty (Lambda2 up md x ty.ty) body.term : Nil
            , app: \md t1 t2 ty -> TermCursor t1.kctx t1.ctx t1.ty (App1 up md t2.term ty.ty) t1.term
                : TermCursor t2.kctx t2.ctx t2.ty (App2 up md t1.term ty.ty) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md x tBinds def defTy body bodyTy -> TermCursor def.kctx def.ctx def.ty (Let1 up md x tBinds defTy.ty body.term bodyTy) def.term
                : TypeCursor defTy.kctx defTy.ctx (Let2 up md x tBinds def.term body.term bodyTy) defTy.ty
                : TermCursor body.kctx body.ctx body.ty (Let3 up md x tBinds def.term defTy.ty bodyTy) body.term : Nil
            , dataa : \md x tbinds ctrs body bodyTy -> TermCursor body.kctx body.ctx body.ty (Data3 up md x tbinds ctrs bodyTy) body.term: Nil
        }
        {kctx, ctx, ty, term}
getCursorChildren (TypeCursor kctx ctx up ty) =
    recType
        {
            arrow: \md t1 t2 -> TypeCursor t1.kctx t1.ctx (Arrow1 up md t2.ty) t1.ty
                : TypeCursor t2.kctx t2.ctx (Arrow2 up md t1.ty) t2.ty : Nil
        }
        {kctx, ctx, ty}

-- the Int is what'th child the input is of the output
up :: CursorLocation -> Maybe (CursorLocation /\ Int)
up (TermCursor kctx ctx ty termPath term) =
    recTermPath
        {
            let1: \up md bind tbinds defTy body bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds term defTy.ty body.term bodyTy) /\ (1 - 1)
            , let3: \up md bind tbinds def defTy bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds def.term defTy.ty term bodyTy) /\ (3 - 1)
            , data3: \up md bind tbinds ctrs bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Data md bind tbinds ctrs term bodyTy) /\ 0 -- for now, since the other children of Data aren't implemented
            , top: Nothing
        }
        {kctx, ctx, ty, termPath}
up (TypeCursor kctx ctx typePath ty) =
    recTypePath
        {
            arrow1: \up md tOut ->
                Just $ TypeCursor up.kctx up.ctx up.typePath (Arrow md ty tOut.ty) /\ (1 - 1)
            , arrow2: \up md tIn ->
                Just $ TypeCursor up.kctx up.ctx up.typePath (Arrow md tIn.ty ty) /\ (2 - 1)
            , let2: \up md bind tbinds def body bodyTy ->
                Just $ TermCursor up.kctx up.ctx up.ty up.termPath (Let md bind tbinds def.term ty body.term bodyTy) /\ (2 - 1)

        }
        {kctx, ctx, ty, typePath}
up _ = hole

stepCursorForwards :: CursorLocation -> CursorLocation
stepCursorForwards cursor = stepCursorForwardsImpl 0 cursor
-- Int is children to step past
stepCursorForwardsImpl :: Int -> CursorLocation -> CursorLocation
stepCursorForwardsImpl childrenSkip cursor =
    let children = getCursorChildren cursor in
    case index children childrenSkip of
    Just child -> child
    Nothing -> case up cursor of
               Just (parent /\ index) -> stepCursorForwardsImpl (index + 1) parent
               Nothing -> cursor -- couldn't move cursor anywhere: no parent or children

--stepCursorBackwards :: CursorLocation -> CursorLocation
