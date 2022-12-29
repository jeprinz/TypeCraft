module TypeCraft.Purescript.CursorMovement where

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
import TypeCraft.Purescript.PathRec
import Data.Maybe (Maybe)
import Data.Maybe (Maybe(..))
import Data.List (length)
import Data.List (index)
import TypeCraft.Purescript.State

getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor ctxs mdty ty up term) =
    recTerm
        {
            lambda: \md x ty body bodyTy -> TermCursor body.ctxs body.mdty body.ty (Lambda3 md x ty.ty bodyTy : up) body.term : Nil
            , app: \md t1 t2 tyArg tyOut -> TermCursor t1.ctxs t1.mdty t1.ty (App1 md t2.term tyArg tyOut : up) t1.term
                : TermCursor t2.ctxs t2.mdty t2.ty (App2 md t1.term tyArg tyOut : up) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md x tBinds def defTy body bodyTy -> TermCursor def.ctxs def.mdty def.ty (Let2 md x tBinds defTy.ty body.term bodyTy : up) def.term
                : TypeCursor defTy.ctxs (Let3 md x tBinds def.term body.term bodyTy : up) defTy.ty
                : TermCursor body.ctxs body.mdty body.ty (Let4 md x tBinds def.term defTy.ty bodyTy : up) body.term : Nil
            , dataa : \md x tbinds ctrs body bodyTy -> TermCursor body.ctxs body.mdty body.ty (Data4 md x tbinds ctrs.ctrs bodyTy : up) body.term: Nil
            , tlet : \md tbind tbinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeCursor def.ctxs (TLet1 md tbind tbinds body.term bodyTy : up) def.ty
                : TermCursor body.ctxs body.mdty body.ty (TLet2 md tbind tbinds def.ty bodyTy : up) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.ctxs t.mdty t.ty (TypeBoundary1 md c : up) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.ctxs t.mdty t.ty (ContextBoundary1 md x c : up) t.term : Nil
            , hole: \md -> Nil
            , buffer: \md def defTy body bodyTy -> Nil
        }
        {ctxs, mdty, ty, term}
getCursorChildren (TypeCursor ctxs up (Arrow md t1 t2)) =
    TypeCursor ctxs (Arrow1 md t2 : up) t1 : TypeCursor ctxs (Arrow2 md t1 : up) t2 : Nil
-- TODO: add TNeu case, which just has no children!
getCursorChildren (TypeCursor ctxs up _) = hole
getCursorChildren (TermBindCursor _ _ _) = Nil

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
parent (TermCursor ctxs mdty ty Nil term) = Nothing
parent (TermCursor ctxs mdty ty termPath term) =
    let mdty = getMDType termPath in
    recTermPath
        {
            let2: \upRec md bind tbinds defTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath (Let md bind tbinds term defTy.ty body.term bodyTy) /\ (1 - 1)
            , let4: \upRec md bind tbinds def defTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath (Let md bind tbinds def.term defTy.ty term bodyTy) /\ (3 - 1)
            , data4: \upRec md bind tbinds ctrs bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath (Data md bind tbinds ctrs term bodyTy) /\ (4 - 1)
        }
        {ctxs, mdty, ty, termPath}
parent (TypeCursor ctxs (Arrow1 md tOut : up) ty) =
    Just $ TypeCursor ctxs up (Arrow md ty tOut) /\ (1 - 1)
parent (TypeCursor ctxs (Arrow2 md tIn : up) ty) =
    Just $ TypeCursor ctxs up (Arrow md tIn ty) /\ (2 - 1)
parent (TypeCursor ctxs (Let3 md bind tbinds def body bodyTy : up) ty) =
    Just $ TermCursor ctxs (getMDType up) ty up(Let md bind tbinds def ty body bodyTy) /\ (2 - 1)
parent _ = hole

stepCursorForwards :: CursorLocation -> CursorLocation
stepCursorForwards cursor = stepCursorForwardsImpl 0 cursor
-- Int is children to step past
stepCursorForwardsImpl :: Int -> CursorLocation -> CursorLocation
stepCursorForwardsImpl childrenSkip cursor =
    let children = getCursorChildren cursor in
    case index children childrenSkip of
    Just child -> child
    Nothing -> case parent cursor of
               Just (parent /\ index) -> stepCursorForwardsImpl (index + 1) parent
               Nothing -> cursor -- couldn't move cursor anywhere: no parent or children

--stepCursorBackwards :: CursorLocation -> CursorLocation
