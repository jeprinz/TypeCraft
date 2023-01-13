module TypeCraft.Purescript.CursorMovement where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.State

import Data.List (List(..), (:))
import Data.List (index)
import Data.List (length)
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermRec

getCursorChildren :: CursorLocation -> List CursorLocation
getCursorChildren (TermCursor ctxs ty up term) =
    recTerm
        {
            lambda: \md x ty body bodyTy ->
                TermBindCursor x.ctxs (Lambda1 md ty.ty body.term bodyTy : up) x.tBind :
                TypeCursor ty.ctxs (Lambda2 md x.tBind body.term bodyTy : up) ty.ty :
                TermCursor body.ctxs body.ty (Lambda3 md x.tBind ty.ty bodyTy : up) body.term : Nil
            , app: \md t1 t2 tyArg tyOut -> TermCursor t1.ctxs t1.ty (App1 md t2.term tyArg tyOut : up) t1.term
                : TermCursor t2.ctxs t2.ty (App2 md t1.term tyArg tyOut : up) t2.term : Nil
            , var: \_ _ _ -> Nil
            , lett: \md tBind tBinds def defTy body bodyTy ->
                TermBindCursor tBind.ctxs (Let1 md {--} tBinds.tyBinds def.term defTy.ty body.term bodyTy : up) tBind.tBind
                : TypeBindListCursor tBinds.ctxs (Let2 md tBind.tBind {--} def.term defTy.ty body.term bodyTy : up) tBinds.tyBinds
                : TermCursor def.ctxs def.ty (Let3 md tBind.tBind tBinds.tyBinds defTy.ty body.term bodyTy : up) def.term
                : TypeCursor defTy.ctxs (Let4 md tBind.tBind tBinds.tyBinds def.term body.term bodyTy : up) defTy.ty
                : TermCursor body.ctxs body.ty (Let5 md tBind.tBind tBinds.tyBinds def.term defTy.ty bodyTy : up) body.term : Nil
            , dataa : \md tBind tyBinds ctrs body bodyTy -> TermCursor body.ctxs body.ty (Data4 md tBind.tyBind tyBinds.tyBinds ctrs.ctrs bodyTy : up) body.term: Nil
            , tlet : \md tbind tyBinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeCursor def.ctxs (TLet3 md tbind.tyBind tyBinds.tyBinds body.term bodyTy : up) def.ty
                : TermCursor body.ctxs body.ty (TLet4 md tbind.tyBind tyBinds.tyBinds def.ty bodyTy : up) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.ctxs t.ty (TypeBoundary1 md c : up) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.ctxs t.ty (ContextBoundary1 md x c : up) t.term : Nil
            , hole: \md -> Nil
            , buffer: \md def defTy body bodyTy -> TermCursor def.ctxs def.ty (Buffer1 md defTy.ty body.term bodyTy : up) def.term
              : TypeCursor defTy.ctxs (Buffer2 md def.term body.term bodyTy : up) defTy.ty
              : TermCursor body.ctxs body.ty (Buffer3 md def.term defTy.ty bodyTy : up) body.term : Nil
        }
        {ctxs, ty, term}
getCursorChildren (TypeCursor ctxs up (Arrow md t1 t2)) =
    TypeCursor ctxs (Arrow1 md t2 : up) t1 : TypeCursor ctxs (Arrow2 md t1 : up) t2 : Nil
getCursorChildren (TypeBindCursor ctxs up _) = Nil
getCursorChildren (TermBindCursor ctxs up _) = Nil
getCursorChildren (TypeCursor ctxs up ty) =
      recType
        ( { arrow: \md ty1 ty2 -> TypeCursor ty1.ctxs (Arrow1 md {--} ty2.ty : up) ty1.ty
            : TypeCursor ty2.ctxs (Arrow2 md ty1.ty {--} : up) ty2.ty: Nil
          , tHole: \md x -> Nil
          , tNeu: \md x tyArgs -> hole' "getCursorChildren"
          }
        )
        {ctxs, ty}
getCursorChildren (CtrListCursor _ _ _) = Nil
getCursorChildren (CtrParamListCursor _ _ _) = Nil
getCursorChildren (TypeArgListCursor _ _ _) = Nil
getCursorChildren (TypeBindListCursor _ _ _) = Nil

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
parent (TermCursor ctxs ty Nil term) = Nothing
parent (TermCursor ctxs ty termPath term) =
    recTermPath
        {
            let3: \upRec md tBind tyBinds defTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , let5: \upRec md tBind tyBinds def defTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (5 - 1)
            , data4: \upRec md bind tyBinds ctrs bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (4 - 1)
            , app1 : \upRec md {-Term-} t2 argTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , app2 : \upRec md t1 {-Term-} argTy bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (2 - 1)
            , lambda3 : \upRec md tbind argTy {-body-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , buffer1 : \upRec md {-Term-} bufTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , buffer3 : \upRec md buf bufTy {-Term-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (3 - 1)
            , typeBoundary1 : \upRec md change {-Term-} ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , contextBoundary1 : \upRec md x change {-Term-} ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (1 - 1)
            , tLet4 : \upRec md tyBind tyBinds def {-Term-} bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (4 - 1)
        }
        {ctxs, ty,  term, termPath}
--parent (TypeCursor ctxs (Arrow1 md tOut : up) ty) =
--    Just $ TypeCursor ctxs up (Arrow md ty tOut) /\ (1 - 1)
--parent (TypeCursor ctxs (Arrow2 md tIn : up) ty) =
--    Just $ TypeCursor ctxs up (Arrow md tIn ty) /\ (2 - 1)
--parent (TypeCursor ctxs (Let4 md bind tyBinds def body bodyTy : up) ty) =
--    Just $ TermCursor ctxs (getMDType up) ty up(Let md bind tyBinds def ty body bodyTy) /\ (2 - 1)
--parent (TypeBindCursor ctxs (TLet1 md {-TypeBind-} tyBinds def body bodyTy : up) tyBind) =
--    Just $ TermCursor ctxs (getMDType up) bodyTy up (TLet md tyBind tyBinds def body bodyTy) /\ (1 - 1)
--parent (TypeBindCursor ctxs (TypeBindListCons1 {-TypeBind-} tyBinds : up) tyBind) =
--    Just $ TypeBindListCursor ctxs up (tyBind : tyBinds) /\ (1 - 1)
parent (TermBindCursor ctxs termBindPath tBind) =
    recTermBindPath
      { lambda1:
          \termPath md argTy body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
      , let1:
          \termPath md tyBinds def defTy body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
      , constructor1:
          \ctrPath md ctrParams -> hole' "parent"
      } {ctxs, tBind, termBindPath}
parent (TypeCursor ctxs typePath ty) =
    recTypePath
      { lambda2:
        \termPath md tBind {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (4 - 1)
        , buffer2: \termPath md def {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , tLet3: \termPath md tyBind tyBinds {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (3 - 1)
        , ctrParam1: \ctrParamPath md {-Type-} -> (hole' "parent")
        , typeArg1: \typeArgPath md {-Type-} -> (hole' "parent")
        , arrow1: \typePath md {-Type-} _ -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ (1 - 1)
        , arrow2: \typePath md _ {-Type-} -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ (2 - 1)
        } {ctxs, typePath, ty}
parent (CtrListCursor _ _ _) = hole' "parent"
parent (CtrParamListCursor _ _ _) = hole' "parent"
parent (TypeArgListCursor _ _ _) = hole' "parent"
parent (TypeBindListCursor ctxs listTypeBindPath tyBinds) =
    recListTypeBindPath ({
        data2 : \termPath md tyBind ctrs body bodyTy -> hole' "parent"
        , tLet2 : \termPath md tyBind def body bodyTy -> hole' "parent"
        , typeBindListCons2 : \listTypeBindPath tyBind -> hole' "parent"
        , let2 : \termPath md tBind def defTy body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
    }) {ctxs, listTypeBindPath, tyBinds}
parent _ = hole' "given an ill-typed upPath to parent function (or I missed a case)"

stepCursorForwards :: CursorLocation -> CursorLocation
stepCursorForwards cursor = case stepCursorForwardsImpl 0 cursor of
    Nothing -> cursor
    Just newCur -> newCur
-- Int is children to step past
stepCursorForwardsImpl :: Int -> CursorLocation -> Maybe CursorLocation
stepCursorForwardsImpl childrenSkip cursor =
    let children = getCursorChildren cursor in
    case index children childrenSkip of
    Just child -> Just child
    Nothing -> case parent cursor of
               Just (parent /\ index) -> stepCursorForwardsImpl (index + 1) parent
               Nothing -> Nothing -- couldn't move cursor anywhere: no parent or children

stepCursorBackwards :: CursorLocation -> CursorLocation
stepCursorBackwards cursor =
    case parent cursor of
        Nothing -> cursor
        Just (par /\ me) ->
            if me == 0 then par else
                case index (getCursorChildren par) (me - 1) of
                    Just newCur -> getLastChild newCur
                    Nothing -> unsafeThrow "shouldn't happen stepCursorBackwards"

getLastChild :: CursorLocation -> CursorLocation
getLastChild cursor =
    let children = getCursorChildren cursor in
    case index children (length children - 1) of
        Nothing -> cursor
        Just child -> getLastChild child

