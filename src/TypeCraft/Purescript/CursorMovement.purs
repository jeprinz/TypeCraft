module TypeCraft.Purescript.CursorMovement where

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

getTyArgCursors :: ListTypeArgRecValue -> List Tooth -> List (CursorLocation)
getTyArgCursors listTypeArg up = recListTypeArg {
    cons : \tyArg tyArgs ->
        recTypeArg {
            typeArg : \md ty -> (TypeCursor tyArg.ctxs (TypeArg1 md : TypeArgListCons1 tyArgs.tyArgs : up) ty.ty)
                : getTyArgCursors tyArgs (TypeArgListCons2 tyArg.tyArg : up)
        } tyArg
    , nil : \_ -> Nil
} listTypeArg

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
            , var: \md x tyArgs -> getTyArgCursors tyArgs (Var1 md x : up)
            , lett: \md tBind tBinds def defTy body bodyTy ->
                TermBindCursor tBind.ctxs (Let1 md {--} tBinds.tyBinds def.term defTy.ty body.term bodyTy : up) tBind.tBind
                : TypeBindListCursor tBinds.ctxs (Let2 md tBind.tBind {--} def.term defTy.ty body.term bodyTy : up) tBinds.tyBinds
                : TypeCursor defTy.ctxs (Let4 md tBind.tBind tBinds.tyBinds def.term body.term bodyTy : up) defTy.ty
                : TermCursor def.ctxs def.ty (Let3 md tBind.tBind tBinds.tyBinds defTy.ty body.term bodyTy : up) def.term
                : TermCursor body.ctxs body.ty (Let5 md tBind.tBind tBinds.tyBinds def.term defTy.ty bodyTy : up) body.term : Nil
            , dataa : \md tyBind tyBinds ctrs body bodyTy ->
                TypeBindCursor tyBind.ctxs (Data1 md {--} tyBinds.tyBinds ctrs.ctrs body.term bodyTy : up) tyBind.tyBind
                : TypeBindListCursor tyBinds.ctxs (Data2 md tyBind.tyBind {--} ctrs.ctrs body.term bodyTy : up) tyBinds.tyBinds
                : CtrListCursor ctrs.ctxs (Data3 md tyBind.tyBind tyBinds.tyBinds {--} body.term bodyTy : up) ctrs.ctrs
                : TermCursor body.ctxs body.ty (Data4 md tyBind.tyBind tyBinds.tyBinds ctrs.ctrs bodyTy : up) body.term: Nil
            , tlet : \md tyBind tyBinds def body bodyTy ->
                -- Add TypeBindList child!
                TypeBindCursor tyBind.ctxs (TLet1 md {-tyBind-} tyBinds.tyBinds def.ty body.term bodyTy : up) tyBind.tyBind
                : TypeBindListCursor tyBinds.ctxs (TLet2 md tyBind.tyBind {-tyBinds-} def.ty body.term bodyTy : up) tyBinds.tyBinds
                : TypeCursor def.ctxs (TLet3 md tyBind.tyBind tyBinds.tyBinds body.term bodyTy : up) def.ty
                : TermCursor body.ctxs body.ty (TLet4 md tyBind.tyBind tyBinds.tyBinds def.ty bodyTy : up) body.term
                : Nil
            , typeBoundary: \md c t -> TermCursor t.ctxs t.ty (TypeBoundary1 md c : up) t.term : Nil
            , contextBoundary: \md x c t -> TermCursor t.ctxs t.ty (ContextBoundary1 md x c : up) t.term : Nil
            , hole: \md -> InsideHoleCursor ctxs ty (Hole1 md : up) : Nil
            , buffer: \md def defTy body bodyTy -> TermCursor def.ctxs def.ty (Buffer1 md defTy.ty body.term bodyTy : up) def.term
              : TypeCursor defTy.ctxs (Buffer2 md def.term body.term bodyTy : up) defTy.ty
              : TermCursor body.ctxs body.ty (Buffer3 md def.term defTy.ty bodyTy : up) body.term : Nil
        }
        {ctxs, ty, term}
getCursorChildren (TypeBindCursor ctxs up _) = Nil
getCursorChildren (TermBindCursor ctxs up _) = Nil
getCursorChildren (TypeCursor ctxs up ty) =
      recType
        ( { arrow: \md ty1 ty2 -> TypeCursor ty1.ctxs (Arrow1 md {--} ty2.ty : up) ty1.ty
            : TypeCursor ty2.ctxs (Arrow2 md ty1.ty {--} : up) ty2.ty: Nil
          , tHole: \md x _ _ -> Nil
          , tNeu: \md x tyArgs -> getTyArgCursors tyArgs (TNeu1 md x : up)
          }
        )
        {ctxs, ty}
getCursorChildren (CtrListCursor ctxs up ctrs) =
    recListCtr ({
        cons: \ctr@{ctr: Constructor md tBind ctrParams} ctrs ->
            TermBindCursor ctr.ctxs (Constructor1 md {--} ctrParams : CtrListCons1 {--} ctrs.ctrs : up) tBind
            : CtrParamListCursor ctr.ctxs (Constructor2 md tBind {--} : CtrListCons1 {--} ctrs.ctrs : up) ctrParams
            : CtrListCursor ctrs.ctxs (CtrListCons2 ctr.ctr {--} : up) ctrs.ctrs : Nil
        , nil: \_ -> Nil
    }) {ctxs, ctrs}
getCursorChildren (CtrParamListCursor ctxs up ctrParams) =
    recListCtrParam ({
        cons: \ctrParam@{ctrParam: (CtrParam md ty)} ctrParams -> TypeCursor ctrParam.ctxs (CtrParam1 md {--} : CtrParamListCons1 {--} ctrParams.ctrParams : up) ty
            : CtrParamListCursor ctrParams.ctxs (CtrParamListCons2 ctrParam.ctrParam {--} : up) ctrParams.ctrParams : Nil
        , nil: \_ -> Nil
    }) {ctxs, ctrParams}
--getCursorChildren (TypeArgListCursor ctxs up tyArgs) =
--    recListTypeArg ({
--        cons: \tyArg@{tyArg: (TypeArg md ty)} tyArgs -> TypeCursor tyArg.ctxs (TypeArg1 md {--} : TypeArgListCons1 {--} tyArgs.tyArgs : up) ty
--            : TypeArgListCursor tyArgs.ctxs (TypeArgListCons2 tyArg.tyArg {--} : up) tyArgs.tyArgs : Nil
--        , nil: Nil
--    }) {ctxs, tyArgs}
getCursorChildren (TypeBindListCursor ctxs up tyBinds) =
    recListTypeBind ({
        cons: \tyBind tyBinds -> TypeBindCursor tyBind.ctxs (TypeBindListCons1 {--} tyBinds.tyBinds : up) tyBind.tyBind
            : TypeBindListCursor tyBinds.ctxs (TypeBindListCons2 tyBind.tyBind {--} : up) tyBinds.tyBinds : Nil
        , nil: \_ -> Nil
    }) {ctxs, tyBinds}
getCursorChildren (InsideHoleCursor _ _ _) = Nil

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
--parent (TermCursor ctxs ty Nil term) = Nothing
parent cursor | (maybe false (\(_ /\ up /\ _) -> null up) (getCursorParts cursor)) = Nothing -- if path is empty
parent (TermCursor ctxs ty termPath term) =
    recTermPath
        {
            let3: \upRec md tBind tyBinds defTy body bodyTy ->
                Just $ TermCursor upRec.ctxs upRec.ty upRec.termPath upRec.term /\ (4 - 1)
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
      , constructor1: \ctrPath md ctrParams ->
          recCtrPath ({ -- We skip the constructor, and the cursor goes to the ctr list above it
              ctrListCons1: \listCtrPath ctrs -> Just $ CtrListCursor listCtrPath.ctxs listCtrPath.listCtrPath listCtrPath.ctrs /\ (1 - 1) -- note that the numbering here is special
          }) ctrPath
      } {ctxs, tBind, termBindPath}
parent (TypeBindCursor ctxs typeBindPath tyBind) =
    recTypeBindPath {
        tLet1 : \termPath md {-tyBind-} tyBinds def body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
        , data1 : \termPath md {-tyBind-} tyBinds ctrs body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
        , typeBindListCons1 : \listTypeBindPath {-tyBind-} tyBind -> Just $ TypeBindListCursor listTypeBindPath.ctxs listTypeBindPath.listTypeBindPath listTypeBindPath.tyBinds /\ (1 - 1)
    } {ctxs, typeBindPath, tyBind}
parent (TypeCursor ctxs typePath ty) =
    recTypePath
      { lambda2:
        \termPath md tBind {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (3 - 1)
        , buffer2: \termPath md def {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , tLet3: \termPath md tyBind tyBinds {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (3 - 1)
        , ctrParam1: \ctrParamPath md {-Type-} ->
            recCtrParamPath ({ -- We skip the CtrParam, and the cursor goes to the CtrParam list above it
                ctrParamListCons1: \listCtrParamPath ctrParams -> Just $ CtrParamListCursor listCtrParamPath.ctxs listCtrParamPath.listCtrParamPath listCtrParamPath.ctrParams /\ (1 - 1)
            }) ctrParamPath
        , typeArg1: \tyArgPath md {-Type-} ->
            let getTyArgChildren :: ListTypeArgPathRecValue -> Int -> Maybe (CursorLocation /\ Int)
                getTyArgChildren tyArgListPath childNum = recListTypeArgPath {
                    tNeu1 : \typePath md tv {-tyArgs-} -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ childNum
                    , typeArgListCons2 : \listTypeArgPath tyArg {-tyArgs-} -> getTyArgChildren listTypeArgPath (childNum + 1)
                    , var1 : \termPath md x {-tyArgs-} -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ childNum
                } tyArgListPath in
            recTypeArgPath {
                typeArgListCons1 : \listTypeArgPath tyArgs -> getTyArgChildren listTypeArgPath 0
            } tyArgPath
--            recTypeArgPath ({ -- We skip the TypeArg, and the cursor goes to the TypeArg list above it
--                typeArgListCons1: \listTypeArgPath tyArgs -> Just $ TypeArgListCursor listTypeArgPath.ctxs listTypeArgPath.listTypeArgPath listTypeArgPath.tyArgs /\ (1 - 1)
--            }) tyArgPath
        , arrow1: \typePath md {-Type-} _ -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ (1 - 1)
        , arrow2: \typePath md _ {-Type-} -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ (2 - 1)
        } {ctxs, typePath, ty}
parent (CtrListCursor ctxs listCtrPath ctrs) =
    recListCtrPath {
        data3: \termPath md tyBind tyBinds body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (3 - 1)
        , ctrListCons2: \listCtrPath ctrs -> Just $ CtrListCursor listCtrPath.ctxs listCtrPath.listCtrPath listCtrPath.ctrs /\ (3 - 1) -- note that the numbering here is special
    } {ctxs, listCtrPath, ctrs}
parent (CtrParamListCursor ctxs listCtrParamPath ctrParams) =
    recListCtrParamPath {
        constructor2: \ctrPath md tBind ->
            recCtrPath ({ -- We skip the constructor, and the cursor goes to the ctr list above it
                ctrListCons1: \listCtrPath ctrs -> Just $ CtrListCursor listCtrPath.ctxs listCtrPath.listCtrPath listCtrPath.ctrs /\ (2 - 1) -- note that the numbering here is special
            }) ctrPath
        , ctrParamListCons2: \listCtrParamPath ctrParam -> Just $ CtrParamListCursor listCtrParamPath.ctxs listCtrParamPath.listCtrParamPath listCtrParamPath.ctrParams /\ (2 - 1)
    } {ctxs, listCtrParamPath, ctrParams}
--parent (TypeArgListCursor ctxs listTypeArgPath tyArgs) =
--    recListTypeArgPath {
--        tNeu1: \typePath md x -> Just $ TypeCursor typePath.ctxs typePath.typePath typePath.ty /\ (1 - 1)
--        , typeArgListCons2: \listTypeArgPath tyArg -> Just $ TypeArgListCursor listTypeArgPath.ctxs listTypeArgPath.listTypeArgPath listTypeArgPath.tyArgs /\ (2 - 1)
--    } {ctxs, listTypeArgPath, tyArgs}
parent (TypeBindListCursor ctxs listTypeBindPath tyBinds) =
    recListTypeBindPath ({
        data2 : \termPath md tyBind ctrs body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , tLet2 : \termPath md tyBind def body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , typeBindListCons2 : \listTypeBindPath tyBind -> Just $ TypeBindListCursor listTypeBindPath.ctxs listTypeBindPath.listTypeBindPath listTypeBindPath.tyBinds /\ (2 - 1)
        , let2 : \termPath md tBind def defTy body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
    }) {ctxs, listTypeBindPath, tyBinds}
parent (InsideHoleCursor ctxs ty insideHolePath) =
    recInsideHolePath ({
        hole1 : \md termPath -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
    }) {ctxs, ty, insideHolePath}
--parent _ = hole' "given an ill-typed upPath to parent function (or I missed a case)"

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

stepCursor_n :: Int -> CursorLocation -> CursorLocation
stepCursor_n n 
    | n < 0 = stepCursorBackwards_n (abs n)
    | n > 0 = stepCursorForwards_n n
    | otherwise = identity

stepCursorBackwards_n :: Int -> CursorLocation -> CursorLocation
stepCursorBackwards_n n loc = Array.foldr identity loc (Array.replicate n stepCursorBackwards)

stepCursorForwards_n :: Int -> CursorLocation -> CursorLocation
stepCursorForwards_n n loc = Array.foldr identity loc (Array.replicate n stepCursorForwards)

getLastChild :: CursorLocation -> CursorLocation
getLastChild cursor =
    let children = getCursorChildren cursor in
    case index children (length children - 1) of
        Nothing -> cursor
        Just child -> getLastChild child

-- TODO: review usages of this function.
getMiddlePath :: Select -> UpPath
getMiddlePath(TermSelect _ _ _ _ middlePath _ _ _ _) = middlePath
getMiddlePath(TypeSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(CtrListSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(CtrParamListSelect _ _ _ middlePath _ _ _) = middlePath
--getMiddlePath(TypeArgListSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(TypeBindListSelect _ _ _ middlePath _ _ _) = middlePath

getPath :: CursorLocation -> UpPath
getPath(TermCursor _ _ path _) = path
getPath(TypeCursor _ path _) = path
getPath(TypeBindCursor _ path _) = path
getPath(TermBindCursor _ path _) = path
getPath(CtrListCursor _ path _) = path
getPath(CtrParamListCursor _ path _) = path
--getPath(TypeArgListCursor _ path _) = path
getPath(TypeBindListCursor _ path _) = path
getPath(InsideHoleCursor _ _ path) = path

data GrammaticalSort = GSTerm | GSType | GSTypeBind | GSTermBind | GSCtrList | GSCtrParamList | GSTypeArgList | GSTypeBindList | GSInnerHole
derive instance genericGrammaticalSort :: Generic GrammaticalSort _
instance eqGrammaticalSort :: Eq GrammaticalSort where
  eq x = genericEq x

data Syn = STerm Type Term | SType Type | SCtrList (List Constructor) | SCtrParamList (List CtrParam) | STypeBindList (List TypeBind)

getCursorParts :: CursorLocation -> Maybe (AllContext /\ UpPath /\ Syn)
getCursorParts (TermCursor ctxs ty up term) = Just $ ctxs /\ up /\ STerm ty term
getCursorParts (TypeCursor ctxs up ty) = Just $ ctxs /\ up /\ SType ty
getCursorParts (CtrListCursor ctxs up ctrs) = Just $ ctxs /\ up /\ SCtrList ctrs
getCursorParts (CtrParamListCursor ctxs up ctrParams) = Just $ ctxs /\ up /\ SCtrParamList ctrParams
getCursorParts (TypeBindListCursor ctxs up tyBinds) = Just $ ctxs /\ up /\ STypeBindList tyBinds
getCursorParts _ = Nothing

partsToCursor :: (AllContext /\ UpPath /\ Syn) -> CursorLocation
partsToCursor (ctxs /\ up /\ syn) = case syn of
    STerm ty term -> TermCursor ctxs ty up term
    SType ty -> TypeCursor ctxs up ty
    SCtrList ctrs -> CtrListCursor ctxs up ctrs
    SCtrParamList ctrParams -> CtrParamListCursor ctxs up ctrParams
    STypeBindList tyBinds -> TypeBindListCursor ctxs up tyBinds

getSelectParts :: Select -> (UpPath /\ AllContext /\ Syn /\ UpPath /\ AllContext /\ Syn /\ Boolean)
getSelectParts (TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 root) = topPath /\ ctxs1 /\ STerm ty1 term1 /\ middlePath /\ ctxs2 /\ STerm ty2 term2 /\ root
getSelectParts (TypeSelect topPath ctxs1 ty1 middlePath ctxs2 ty2 root) = topPath /\ ctxs1 /\ SType ty1 /\ middlePath /\ ctxs2 /\ SType ty2 /\ root
getSelectParts (CtrListSelect topPath ctxs1 ctrs1 middlePath ctxs2 ctrs2 root) = topPath /\ ctxs1 /\ SCtrList ctrs1 /\ middlePath /\ ctxs2 /\ SCtrList ctrs2 /\ root
getSelectParts (CtrParamListSelect topPath ctxs1 ctrParams1 middlePath ctxs2 ctrParams2 root) = topPath /\ ctxs1 /\ SCtrParamList ctrParams1 /\ middlePath /\ ctxs2 /\ SCtrParamList ctrParams2 /\ root
getSelectParts (TypeBindListSelect topPath ctxs1 tyBinds1 middlePath ctxs2 tyBinds2 root) = topPath /\ ctxs1 /\ STypeBindList tyBinds1 /\ middlePath /\ ctxs2 /\ STypeBindList tyBinds2 /\ root

partsToSelect :: (UpPath /\ AllContext /\ Syn /\ UpPath /\ AllContext /\ Syn /\ Boolean) -> Select
partsToSelect (topPath /\ ctxs1 /\ syn1 /\ middlePath /\ ctxs2 /\ syn2 /\ root) = case syn1 /\ syn2 of
    STerm ty1 term1 /\ STerm ty2 term2 -> TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 root
    SType ty1 /\ SType ty2-> TypeSelect topPath ctxs1 ty1 middlePath ctxs2 ty2 root
    SCtrList ctrs1 /\ SCtrList ctrs2 -> CtrListSelect topPath ctxs1 ctrs1 middlePath ctxs2 ctrs2 root
    SCtrParamList ctrParams1 /\ SCtrParamList ctrParams2 -> CtrParamListSelect topPath ctxs1 ctrParams1 middlePath ctxs2 ctrParams2 root
    STypeBindList tyBinds1 /\ STypeBindList tyBinds2 -> TypeBindListSelect topPath ctxs1 tyBinds1 middlePath ctxs2 tyBinds2 root
    _ -> unsafeThrow "shouldn't happen in partsToSelect"

moveSelectLeft :: Select -> Maybe Mode
moveSelectLeft select =
    let (topPath /\ ctxs1 /\ syn1 /\ middlePath /\ ctxs2 /\ syn2 /\ ori) = getSelectParts select in
    case ori of
        false {-botSelectOrientation-} -> case topPath of
            Nil -> Nothing
            (tooth : topPath') ->
                let middlePath' = middlePath <> (tooth : Nil) in
                let par /\ _ = fromJust $ parent (partsToCursor (ctxs1 /\ topPath /\ syn1)) in
                if (getCursorSort par == sortFromSyn syn1) then
                    let (ctxs1' /\ topPath' /\ syn1') = fromJust $ getCursorParts par in
                    Just $ SelectMode {select: partsToSelect (topPath' /\ ctxs1' /\ syn1' /\ middlePath' /\ ctxs2 /\ syn2 /\ botSelectOrientation)}
                else Nothing
        true {-topSelectOrientation-} ->
            case (goLeftUntilSort (sortFromSyn syn1) (partsToCursor (ctxs2 /\ middlePath /\ syn2))) of
                Just cursor ->
                    let (ctxs2' /\ middlePath' /\ syn2') = fromJust $ getCursorParts cursor in
                    Just $ SelectMode $ {select: partsToSelect (topPath /\ ctxs1 /\ syn1 /\ middlePath' /\ ctxs2' /\ syn2' /\ topSelectOrientation)}
                Nothing -> Just $ makeCursorMode $ (partsToCursor (ctxs1 /\ topPath /\ syn1))

moveSelectRight :: Select -> Maybe Mode
moveSelectRight select =
    let (topPath /\ ctxs1 /\ syn1 /\ middlePath /\ ctxs2 /\ syn2 /\ ori) = getSelectParts select in
    case ori of
        false {-botSelectOrientation-} -> case middlePath of
            Nil -> unsafeThrow "Shouldn't be an empty selection"
            (tooth : Nil) -> Just $ makeCursorMode $ partsToCursor (ctxs2 /\ (tooth : topPath) /\ syn2)
            middlePath ->
                let tooth = fromJust $ last middlePath in
                let middlePath' = fromJust $ init middlePath in
                let children = getCursorChildren (partsToCursor (ctxs1 /\ topPath /\ syn1)) in
                let particularChild = fromJust $ find (\cursor -> head' (getPath cursor) == tooth) children in -- get the child who's top tooth is equal to "tooth"
                let (ctxs1' /\ topPath' /\ syn1') = fromJust $ getCursorParts particularChild in
                Just $ SelectMode {select: partsToSelect (topPath' /\ ctxs1' /\ syn1' /\ middlePath' /\ ctxs2 /\ syn2 /\ botSelectOrientation)}
        true {-topSelectOrientation-} ->
                do cursor <- (goRightUntilSort (sortFromSyn syn1) (partsToCursor (ctxs2 /\ middlePath /\ syn2)))
                   let (ctxs2' /\ middlePath' /\ syn2') = fromJust $ getCursorParts cursor
                   Just $ SelectMode {select: partsToSelect (topPath /\ ctxs1 /\ syn1 /\ middlePath' /\ ctxs2' /\ syn2' /\ topSelectOrientation)}

sortFromSyn :: Syn -> GrammaticalSort
sortFromSyn (STerm _ _) = GSTerm
sortFromSyn (SType _) = GSType
sortFromSyn (SCtrList _) = GSCtrList
sortFromSyn (SCtrParamList _) = GSCtrParamList
sortFromSyn (STypeBindList _) = GSTypeBindList

getCursorSort :: CursorLocation -> GrammaticalSort
getCursorSort(TermCursor _ _ _ _) = GSTerm
getCursorSort(TypeCursor _ _ _) = GSType
getCursorSort(TypeBindCursor _ _ _) = GSTypeBind
getCursorSort(TermBindCursor _ _ _) = GSTermBind
getCursorSort(CtrListCursor _ _ _) = GSCtrList
getCursorSort(CtrParamListCursor _ _ _) = GSCtrParamList
--getCursorSort(TypeArgListCursor _ _ _) = GSTypeArgList
getCursorSort(TypeBindListCursor _ _ _) = GSTypeBindList
getCursorSort(InsideHoleCursor _ _ _) = GSInnerHole

-- If this returns Nothing, then should exit Select mode and go to Cursor mode
goLeftUntilSort :: GrammaticalSort -> CursorLocation -> Maybe CursorLocation
goLeftUntilSort sort cursor =
    let cursor' = stepCursorBackwards cursor in
    if not (getCursorSort cursor' == sort) then goLeftUntilSort sort cursor'
    else
        if null (getPath cursor') then Nothing else Just cursor'

{-
I believe that it should always be the case for each sort of Selection that if you go right far enough, you will find something
of the correct sort. This is merely a quirk of our grammar, not something that is generally necessarily true.
-}
goRightUntilSort :: GrammaticalSort -> CursorLocation -> Maybe CursorLocation
goRightUntilSort sort cursor =
---- Int is children to step past
--stepCursorForwardsImpl :: Int -> CursorLocation -> Maybe CursorLocation
    case stepCursorForwardsImpl 0 cursor of
        Just cursor' ->
            if not (getCursorSort cursor' == sort) then goRightUntilSort sort cursor'
            else Just cursor'
        Nothing -> Nothing

{-
Possible plan for writing the Cursor Movement code without quite so much repetition:
GenericCursor t = GrammaticalSort x UpPath x t
Then, can use parent and getCursorChildren on GenericCursor

Then,
moveSelectTopLeft t :: GrammaticalSort ->
-}

cursorLocationToSelect :: SelectOrientation -> CursorLocation -> Maybe Select
--cursorLocationToSelect ori = case _ of
--  TermCursor ctxs ty tmPath tm -> TermSelect tmPath ctxs ty tm Nil ctxs ty tm ori
--  _ -> hole' "cursorLocationToSelect: other cases"
cursorLocationToSelect ori cursor = do
    (ctxs /\ up /\ syn) <- getCursorParts cursor
    pure $ partsToSelect (up /\ ctxs /\ syn /\ Nil /\ ctxs /\ syn /\ ori)

goUp_n :: Int -> CursorLocation -> CursorLocation
goUp_n n loc 
    | n == 0 = loc 
    | otherwise = case parent loc of 
        Nothing -> loc 
        Just (loc' /\ _) -> goUp_n (n - 1) loc'
