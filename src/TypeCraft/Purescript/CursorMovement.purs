module TypeCraft.Purescript.CursorMovement where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
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
import Effect.Exception.Unsafe (unsafeThrow)

getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor ctxs mdty ty up term) =
    recTerm
        {
            lambda: \md x ty body bodyTy -> TermCursor body.ctxs body.mdty body.ty (Lambda3 md x.tBind ty.ty bodyTy : up) body.term : Nil
            , app: \md t1 t2 tyArg tyOut -> TermCursor t1.ctxs t1.mdty t1.ty (App1 md t2.term tyArg tyOut : up) t1.term
                : TermCursor t2.ctxs t2.mdty t2.ty (App2 md t1.term tyArg tyOut : up) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md x tBinds def defTy body bodyTy -> TermCursor def.ctxs def.mdty def.ty (Let2 md x.tBind tBinds.tyBinds defTy.ty body.term bodyTy : up) def.term
                : TypeCursor defTy.ctxs (Let3 md x.tBind tBinds.tyBinds def.term body.term bodyTy : up) defTy.ty
                : TermCursor body.ctxs body.mdty body.ty (Let4 md x.tBind tBinds.tyBinds def.term defTy.ty bodyTy : up) body.term : Nil
            , dataa : \md x tyBinds ctrs body bodyTy -> TermCursor body.ctxs body.mdty body.ty (Data4 md x.tyBind tyBinds.tyBinds ctrs.ctrs bodyTy : up) body.term: Nil
            , tlet : \md tbind tyBinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeCursor def.ctxs (TLet3 md tbind.tyBind tyBinds.tyBinds body.term bodyTy : up) def.ty
                : TermCursor body.ctxs body.mdty body.ty (TLet4 md tbind.tyBind tyBinds.tyBinds def.ty bodyTy : up) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.ctxs t.mdty t.ty (TypeBoundary1 md c : up) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.ctxs t.mdty t.ty (ContextBoundary1 md x c : up) t.term : Nil
            , hole: \md -> Nil
            , buffer: \md def defTy body bodyTy -> TermCursor def.ctxs def.mdty def.ty (Buffer1 md defTy.ty body.term bodyTy : up) def.term
              : TypeCursor defTy.ctxs (Buffer2 md def.term body.term bodyTy : up) defTy.ty
              : TermCursor body.ctxs body.mdty body.ty (Buffer3 md def.term defTy.ty bodyTy : up) body.term : Nil
        }
        {ctxs, mdty, ty, term}
getCursorChildren (TypeCursor ctxs up (Arrow md t1 t2)) =
    TypeCursor ctxs (Arrow1 md t2 : up) t1 : TypeCursor ctxs (Arrow2 md t1 : up) t2 : Nil
getCursorChildren (TypeBindCursor ctxs up _) = hole
getCursorChildren (TermBindCursor ctxs up _) = hole
getCursorChildren (TypeCursor ctxs up _) = hole
getCursorChildren (CtrListCursor _ _ _) = Nil
getCursorChildren (CtrParamListCursor _ _ _) = Nil
getCursorChildren (TypeArgListCursor _ _ _) = Nil
getCursorChildren (TypeBindListCursor _ _ _) = Nil

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
parent (TermCursor ctxs mdty ty Nil term) = Nothing
parent (TermCursor ctxs mdty ty termPath term) =
    let mdty = getMDType termPath in
    recTermPath
        {
            let2: \upRec md tBind tyBinds defTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , let4: \upRec md tBind tyBinds def defTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , data4: \upRec md bind tyBinds ctrs bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (4 - 1)
            , app1 : \upRec md {-Term-} t2 argTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , app2 : \upRec md t1 {-Term-} argTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (2 - 1)
            , lambda3 : \upRec md tbind argTy {-body-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , buffer1 : \upRec md {-Term-} bufTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , buffer3 : \upRec md buf bufTy {-Term-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , typeBoundary1 : \upRec md change {-Term-} ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , contextBoundary1 : \upRec md x change {-Term-} ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , tLet4 : \upRec md tyBind tyBinds def {-Term-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.mdty upRec.ty upRec.termPath upRec.term /\ (4 - 1)
        }
        {ctxs, mdty, ty, term, termPath}
parent (TypeCursor ctxs (Arrow1 md tOut : up) ty) =
    Just $ TypeCursor ctxs up (Arrow md ty tOut) /\ (1 - 1)
parent (TypeCursor ctxs (Arrow2 md tIn : up) ty) =
    Just $ TypeCursor ctxs up (Arrow md tIn ty) /\ (2 - 1)
parent (TypeCursor ctxs (Let3 md bind tyBinds def body bodyTy : up) ty) =
    Just $ TermCursor ctxs (getMDType up) ty up(Let md bind tyBinds def ty body bodyTy) /\ (2 - 1)
parent (TypeBindCursor ctxs (TLet1 md {-TypeBind-} tyBinds def body bodyTy : up) tyBind) =
    Just $ TermCursor ctxs (getMDType up) bodyTy up (TLet md tyBind tyBinds def body bodyTy) /\ (1 - 1)
parent (TypeBindCursor ctxs (TypeBindListCons1 {-TypeBind-} tyBinds : up) tyBind) =
    Just $ TypeBindListCursor ctxs up (tyBind : tyBinds) /\ (1 - 1)
parent (TermBindCursor ctxs up _) = hole
parent (TypeCursor ctxs up _) = hole
parent (CtrListCursor _ _ _) = hole
parent (CtrParamListCursor _ _ _) = hole
parent (TypeArgListCursor _ _ _) = hole
parent (TypeBindListCursor _ _ _) = hole
parent _ = unsafeThrow "given an ill-typed upPath to parent function (or I missed a case)"

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
