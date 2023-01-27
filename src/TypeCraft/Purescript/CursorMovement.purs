module TypeCraft.Purescript.CursorMovement where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec

import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:), find, last, init)
import Data.List (head)
import Data.List (index)
import Data.List (length)
import Data.Maybe (Maybe(..))
import Data.Maybe (Maybe)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Util (fromJust, hole, hole')
import TypeCraft.Purescript.Util (head')

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
            , hole: \md -> Nil
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
          , tHole: \md x -> Nil
          , tNeu: \md x tyArgs -> hole' "getCursorChildren"
          }
        )
        {ctxs, ty}
getCursorChildren (CtrListCursor _ _ _) = Nil -- hole
getCursorChildren (CtrParamListCursor _ _ _) = Nil -- hole
getCursorChildren (TypeArgListCursor ctxs up tyArgs) =
    recListTypeArg ({
        cons: \tyArg@{tyArg: (TypeArg md ty)} tyArgs -> TypeCursor tyArg.ctxs (TypeArg1 md {--} : TypeArgListCons1 {--} tyArgs.tyArgs : up) ty
            : TypeArgListCursor tyArgs.ctxs (TypeArgListCons2 tyArg.tyArg {--} : up) tyArgs.tyArgs : Nil
        , nil: Nil
    }) {ctxs, tyArgs}
getCursorChildren (TypeBindListCursor ctxs up tyBinds) =
    recListTypeBind ({
        cons: \tyBind tyBinds -> TypeBindCursor tyBind.ctxs (TypeBindListCons1 {--} tyBinds.tyBinds : up) tyBind.tyBind
            : TypeBindListCursor tyBinds.ctxs (TypeBindListCons2 tyBind.tyBind {--} : up) tyBinds.tyBinds : Nil
        , nil: Nil
    }) {ctxs, tyBinds}

-- the Int is what'th child the input is of the output
parent :: CursorLocation -> Maybe (CursorLocation /\ Int)
parent (TermCursor ctxs ty Nil term) = Nothing
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
      , constructor1:
          \ctrPath md ctrParams -> hole' "parent"
      } {ctxs, tBind, termBindPath}
parent (TypeBindCursor ctxs typeBindPath tyBind) =
    recTypeBindPath {
        tLet1 : \termPath md {-tyBind-} tyBinds def body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
        , data1 : \termPath md {-tyBind-} tyBinds ctrs body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (1 - 1)
        , typeBindListCons1 : \listTypeBindPath {-tyBind-} tyBind -> hole' "parent"
    } {ctxs, typeBindPath, tyBind}
parent (TypeCursor ctxs typePath ty) =
    recTypePath
      { lambda2:
        \termPath md tBind {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (3 - 1)
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
        data2 : \termPath md tyBind ctrs body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
        , tLet2 : \termPath md tyBind def body bodyTy -> Just $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term /\ (2 - 1)
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

moveSelectLeft :: Select -> Maybe Mode
moveSelectLeft (TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 false)  =
    case topPath of
    Nil -> Nothing
    (tooth : topPath') ->
        let middlePath' = middlePath <> (tooth : Nil) in
        case parent (TermCursor ctxs1 ty1 topPath term1) of
            Just (TermCursor ctxs1' ty1' topPath' term1' /\ _) ->
                Just $ SelectMode {select: TermSelect topPath' ctxs1' ty1' term1' middlePath' ctxs2 ty2 term2 botSelectOrientation}
            _ -> unsafeThrow "Shouldn't happen moveSelectLeft" -- This shouldn't happen because there can be nothing above a term other than more terms!
moveSelectLeft(TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 true)  =
    case  (goLeftUntilSort GSTerm (TermCursor ctxs2 ty2 middlePath term2)) of
        Just (TermCursor ctxs2' ty2' middlePath' term2') -> Just $ SelectMode $ {select: TermSelect topPath ctxs1 ty1 term1 middlePath' ctxs2' ty2' term2' topSelectOrientation} 
        Nothing -> Just $ makeCursorMode $ TermCursor ctxs1 ty1 topPath term1 -- enter cursor mode
        Just _ -> unsafeThrow "Shouldn't happen 1"
moveSelectLeft(TypeSelect topPath ctxs1 ty1 middlePath ctxs2 ty2 root)  = hole' "moveSelectTopUp"
moveSelectLeft(CtrListSelect topPath ctxs1 ctrs1 middlePath ctxs2 ctrs2 root)  = hole' "moveSelectTopUp"
moveSelectLeft(CtrParamListSelect topPath ctxs1 ctrParams1 middlePath ctxs2 ctrParams2 root)  = hole' "moveSelectTopUp"
moveSelectLeft(TypeArgListSelect topPath ctxs1 tyArgs1 middlePath ctxs2 tyArgs2 root)  = hole' "moveSelectTopUp"
moveSelectLeft(TypeBindListSelect topPath ctxs1 tyBinds1 middlePath ctxs2 tyBinds2 root)  = hole' "moveSelectTopUp"

moveSelectRight :: Select -> Maybe Mode
moveSelectRight(TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 false)  =
    case middlePath of
    Nil -> unsafeThrow "Shouldn't be an empty selection"
    (tooth : Nil) -> Just $ makeCursorMode $ TermCursor ctxs2 ty2 (tooth : topPath) term2 -- in this case, we exit select mode and enter cursor mode
    middlePath ->
        let tooth = fromJust $ last middlePath in
        let middlePath' = fromJust $ init middlePath in
--        let topPath' = tooth : topPath in
        let children = getCursorChildren (TermCursor ctxs1 ty1 topPath term1) in
        let particularChild = fromJust $ find (\cursor -> head' (getPath cursor) == tooth) children in -- get the child who's top tooth is equal to "tooth"
        case particularChild of
            TermCursor ctxs1' ty1' topPath' term1' ->
                Just $ SelectMode
                    {select: TermSelect topPath' ctxs1' ty1' term1' middlePath' ctxs2 ty2 term2 botSelectOrientation}
            _ -> unsafeThrow "SHouldn't happen"
moveSelectRight(TermSelect topPath ctxs1 ty1 term1 middlePath ctxs2 ty2 term2 true) =
    case  (goRightUntilSort GSTerm (TermCursor ctxs2 ty2 middlePath term2)) of
        TermCursor ctxs2' ty2' middlePath' term2' -> Just $ SelectMode $ {select: TermSelect topPath ctxs1 ty1 term1 middlePath' ctxs2' ty2' term2' topSelectOrientation}
        badCursor -> unsafeThrow ("Shouldn't happen: got " <> show badCursor)
moveSelectRight(TypeSelect topPath ctxs1 ty1 middlePath ctxs2 ty2 root)  = hole' "moveSelectTopUp"
moveSelectRight(CtrListSelect topPath ctxs1 ctrs1 middlePath ctxs2 ctrs2 root)  = hole' "moveSelectTopUp"
moveSelectRight(CtrParamListSelect topPath ctxs1 ctrParams1 middlePath ctxs2 ctrParams2 root)  = hole' "moveSelectTopUp"
moveSelectRight(TypeArgListSelect topPath ctxs1 tyArgs1 middlePath ctxs2 tyArgs2 root)  = hole' "moveSelectTopUp"
moveSelectRight(TypeBindListSelect topPath ctxs1 tyBinds1 middlePath ctxs2 tyBinds2 root)  = hole' "moveSelectTopUp"

getMiddlePath :: Select -> UpPath
getMiddlePath(TermSelect _ _ _ _ middlePath _ _ _ _) = middlePath
getMiddlePath(TypeSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(CtrListSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(CtrParamListSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(TypeArgListSelect _ _ _ middlePath _ _ _) = middlePath
getMiddlePath(TypeBindListSelect _ _ _ middlePath _ _ _) = middlePath

getPath :: CursorLocation -> UpPath
getPath(TermCursor _ _ path _) = path
getPath(TypeCursor _ path _) = path
getPath(TypeBindCursor _ path _) = path
getPath(TermBindCursor _ path _) = path
getPath(CtrListCursor _ path _) = path
getPath(CtrParamListCursor _ path _) = path
getPath(TypeArgListCursor _ path _) = path
getPath(TypeBindListCursor _ path _) = path

data GrammaticalSort = GSTerm | GSType | GSTypeBind | GSTermBind | GSCtrList | GSCtrParamList | GSTypeArgList | GSTypeBindList
derive instance genericGrammaticalSort :: Generic GrammaticalSort _
instance eqGrammaticalSort :: Eq GrammaticalSort where
  eq x = genericEq x

getCursorSort :: CursorLocation -> GrammaticalSort
getCursorSort(TermCursor _ _ _ _) = GSTerm
getCursorSort(TypeCursor _ _ _) = GSType
getCursorSort(TypeBindCursor _ _ _) = GSTypeBind
getCursorSort(TermBindCursor _ _ _) = GSTermBind
getCursorSort(CtrListCursor _ _ _) = GSCtrList
getCursorSort(CtrParamListCursor _ _ _) = GSCtrParamList
getCursorSort(TypeArgListCursor _ _ _) = GSTypeArgList
getCursorSort(TypeBindListCursor _ _ _) = GSTypeBindList

-- If this returns Nothing, then should exit Select mode and go to Cursor mode
goLeftUntilSort :: GrammaticalSort -> CursorLocation -> Maybe CursorLocation
goLeftUntilSort sort cursor =
    let cursor' = stepCursorBackwards cursor in
    if not (getCursorSort cursor' == sort) then goLeftUntilSort sort cursor'
    else
        if getPath cursor' == Nil then Nothing else Just cursor'

{-
I believe that it should always be the case for each sort of Selection that if you go right far enough, you will find something
of the correct sort. This is merely a quirk of our grammar, not something that is generally necessarily true.
-}
goRightUntilSort :: GrammaticalSort -> CursorLocation -> CursorLocation
goRightUntilSort sort cursor =
    let cursor' = stepCursorForwards cursor in
    if not (getCursorSort cursor' == sort) then goRightUntilSort sort cursor'
    else cursor'


{-
Possible plan for writing the Cursor Movement code without quite so much repetition:
GenericCursor t = GrammaticalSort x UpPath x t
Then, can use parent and getCursorChildren on GenericCursor

Then,
moveSelectTopLeft t :: GrammaticalSort ->
-}

{-When you start a selection going left from a cursor, you always are going to the parent.-}
selectLeftFromCursor :: CursorLocation -> Maybe Select
selectLeftFromCursor cursor@(TermCursor ctxs ty (tooth : path) term) =
    case parent cursor of
        Nothing -> Nothing
        Just (TermCursor ctxs1 ty1 path1 term1 /\ _) -> Just $ TermSelect path1 ctxs1 ty1 term1 (tooth : Nil) ctxs ty term botSelectOrientation
        Just _ -> unsafeThrow "shouldn't happen"
selectLeftFromCursor (TypeCursor ctxs (tooth : path) ty) = hole' "selectLeftFromCursor"
selectLeftFromCursor (CtrListCursor ctxs (tooth : path) ctrs) = hole' "selectLeftFromCursor"
selectLeftFromCursor (CtrParamListCursor ctxs (tooth : path) ctrParams) = hole' "selectLeftFromCursor"
selectLeftFromCursor (TypeArgListCursor ctxs (tooth : path) tyArgs) = hole' "selectLeftFromCursor"
selectLeftFromCursor (TypeBindListCursor ctxs (tooth : path) tyBinds) = hole' "selectLeftFromCursor"
selectLeftFromCursor _ = Nothing

selectRightFromCursor :: CursorLocation -> Maybe Select
selectRightFromCursor cursor@(TermCursor ctxs ty path term) =
    case head (getCursorChildren cursor) of
        Nothing -> Nothing
        Just (TermCursor ctxs1 ty1 (tooth : _path) term1) ->
            Just $ TermSelect path ctxs ty term (tooth : Nil) ctxs1 ty1 term1 topSelectOrientation
        Just _ -> unsafeThrow "shouldn't happen"
selectRightFromCursor (TypeCursor ctxs (tooth : path) ty) = hole' "selectRightFromCursor"
selectRightFromCursor (CtrListCursor ctxs (tooth : path) ctrs) = hole' "selectRightFromCursor"
selectRightFromCursor (CtrParamListCursor ctxs (tooth : path) ctrParams) = hole' "selectRightFromCursor"
selectRightFromCursor (TypeArgListCursor ctxs (tooth : path) tyArgs) = hole' "selectRightFromCursor"
selectRightFromCursor (TypeBindListCursor ctxs (tooth : path) tyBinds) = hole' "selectRightFromCursor"
selectRightFromCursor _ = Nothing
