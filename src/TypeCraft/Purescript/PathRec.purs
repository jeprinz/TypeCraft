module TypeCraft.Purescript.PathRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Map.Internal (empty, lookup, insert, union)

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, delete, filterKeys)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange, invertVarChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import Data.Tuple (fst)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermRec
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCtxVarChange)

type TermPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ty :: Type, term :: Term, termPath :: UpPath}
type TypePathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ty :: Type, typePath :: UpPath}
type CtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ctr :: Constructor, ctrPath :: UpPath}
type CtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ctrParam :: CtrParam, ctrParamPath :: UpPath}
type TypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, tyArg :: TypeArg, typeArgPath :: UpPath}
type TypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, tyBind :: TypeBind, typeBindPath :: UpPath}
type TermBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, tBind :: TermBind, termBindPath :: UpPath}
type ListCtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ctrs :: List Constructor, listCtrPath :: UpPath}
type ListCtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ctrParams :: List CtrParam, listCtrParamPath :: UpPath}
type ListTypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, tyArgs :: List TypeArg, listTypeArgPath :: UpPath}
type ListTypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, topmd :: MDType, tyBinds :: List TypeBind, listTypeBindPath :: UpPath}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let3), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let2 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , let4 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> Type -> a
    , app1 :: TermPathRecValue -> AppMD -> TermRecValue -> Type -> Type -> a
    , app2 :: TermPathRecValue -> AppMD -> TermRecValue -> Type -> Type -> a
    , lambda3 :: TermPathRecValue -> LambdaMD -> TermBind -> TypeRecValue -> Type -> a
    , buffer1 :: TermPathRecValue -> BufferMD -> TypeRecValue -> TermRecValue -> Type -> a
    , buffer3 :: TermPathRecValue -> BufferMD -> TermRecValue -> TypeRecValue -> Type -> a
    , typeBoundary1 :: TermPathRecValue -> TypeBoundaryMD -> Change -> a
    , contextBoundary1 :: TermPathRecValue -> ContextBoundaryMD -> TermVarID -> VarChange -> a
    , tLet4 :: TermPathRecValue -> TLetMD -> TypeBind -> ListTypeBindRecValue -> TypeRecValue -> Type -> a
    , data4 :: TermPathRecValue -> GADTMD -> TypeBind -> ListTypeBindRecValue -> ListCtrRecValue -> Type -> a
}

-- TODO: need to get indentation!
getMDType :: MDType -> UpPath -> MDType
--getMDType (App1 _ _ _ _ : _ : _) = defaultMDType{onLeftOfApp = true}
--getMDType (App2 _ _ _ _ : _ : _) = defaultMDType{onRightOfApp = true}
--getMDType (Arrow1 _ _ : _ : _) = defaultMDType{onLeftOfArrow = true}
--getMDType _ = defaultMDType
--getMDType Nil
getMDType topmetadata Nil = topmetadata
getMDType topmetadata (parent : _) = getMDOfToothChild parent

getMDOfToothChild :: Tooth -> MDType
getMDOfToothChild (App1 _ _ _ _) = defaultMDType{onLeftOfApp = true}
getMDOfToothChild (App2 _ _ _ _) = defaultMDType{onRightOfApp = true}
getMDOfToothChild (Arrow1 _ _) = defaultMDType{onLeftOfArrow = true}
getMDOfToothChild _ = defaultMDType


recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {topmd, ctxs, ty, term, termPath: (Let2 md tBind@(TermBind xmd x) tyBinds {-Term-} defTy body bodyTy) : up} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let2 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: bodyTy, term: Let md tBind tyBinds term defTy body bodyTy, termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (Let4 md tBind@(TermBind _ x) tyBinds def defTy {-Term-} bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let4 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: ty, term: (Let md tBind tyBinds def defTy term bodyTy), termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: defTy, term: def} --def
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (App1 md {-Term-} t2 argTy outTy) : up} =
    if not (Arrow defaultArrowMD argTy outTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app1 {topmd, ctxs, mdty: getMDType topmd up, ty: outTy, term: App md term t2 argTy outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onRightOfApp= true}, ty: argTy, term: t2}
        argTy outTy
recTermPath args {topmd, ctxs, ty, term, termPath: (App2 md t1 {-Term-} argTy outTy) : up} =
    if not (argTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app2 {topmd, ctxs, mdty: getMDType topmd up, ty: outTy, term: App md t1 term argTy outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onLeftOfApp= true}, ty: Arrow defaultArrowMD argTy outTy, term: t1}
        argTy outTy
recTermPath args {topmd, ctxs, ty, term, termPath: (Lambda3 md tbind@(TermBind _ x) argTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx= delete x ctxs.mdctx, ctx= delete x ctxs.ctx} in
    args.lambda3 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: Arrow defaultArrowMD argTy bodyTy, term: Lambda md tbind argTy term bodyTy, termPath: up}
        md tbind {ctxs: ctxs', mdty: defaultMDType, ty: argTy}
        bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (Buffer1 md {-Term-} bufTy body bodyTy) : up} =
    if not (bufTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer1 {topmd, ctxs, mdty: getMDType topmd up, ty: bodyTy, term: Buffer md term bufTy body bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (Buffer3 md buf bufTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer3 {topmd, ctxs, mdty: getMDType topmd up, ty: bodyTy, term: Buffer md buf bufTy term bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy, term: buf}
        {ctxs, mdty: defaultMDType, ty: bufTy} bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (TypeBoundary1 md c {-Term-}) : up} =
    args.typeBoundary1 {topmd, ctxs, mdty: getMDType topmd up, ty: ty, term: TypeBoundary md c term, termPath: up} md c
recTermPath args {topmd, ctxs, ty, term, termPath: (ContextBoundary1 md x c) : up} =
    let ctxs' = ctxs{ctx = alterCtxVarChange ctxs.ctx x (invertVarChange c)} in
    args.contextBoundary1 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: ty, term: ContextBoundary md x c term, termPath: up} md x c
recTermPath args {topmd, ctxs, ty, term, termPath: (TLet4 md tybind@(TypeBind _ x) tyBinds def {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs {mdkctx = delete x ctxs.mdkctx, kctx = delete x ctxs.kctx} in
    args.tLet4 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: bodyTy, term: TLet md tybind tyBinds def term bodyTy, termPath: up}
        md tybind {ctxs, mdty: defaultMDType, tyBinds} {ctxs: ctxs', mdty: defaultMDType, ty: def} bodyTy
recTermPath args {topmd, ctxs, ty, term, termPath: (Data4 md tyBind@(TypeBind _ x) tyBinds ctrs {-Term-} bodyTy) : up} =
    let ctxs' = removeDataFromCtx ctxs tyBind tyBinds ctrs in
    args.data4 {topmd, ctxs: ctxs', mdty: getMDType topmd up, ty: bodyTy, term: Data md tyBind tyBinds ctrs term bodyTy, termPath: up}
        md tyBind {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ctrs} bodyTy
recTermPath _ _ = unsafeThrow "recTermPath given something that isn't a term path"

type TypePathRec a = {
      lambda2 :: TermPathRecValue -> LambdaMD -> TermBindRecValue -> TermRecValue -> Type -> a
      , let3 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TermRecValue -> Type -> a
      , buffer2 :: TermPathRecValue -> BufferMD -> TermRecValue -> TermRecValue -> Type -> a
      , tLet3 :: TermPathRecValue -> TLetMD -> TypeBindRecValue -> ListTypeBindRecValue -> TermRecValue -> Type -> a
      , ctrParam1 :: CtrParamPathRecValue -> CtrParamMD -> a
      , typeArg1 :: TypeArgPathRecValue -> TypeArgMD -> a
      , arrow1 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
      , arrow2 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
}

recTypePath :: forall a. TypePathRec a -> TypePathRecValue -> a
recTypePath args {topmd, ctxs, ty, typePath: (Lambda2 md tBind@(TermBind xmd x) {-Type-} body bodyTy) : termPath} =
  let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType ty) ctxs.ctx} in
    args.lambda2 {topmd, ctxs, ty: Arrow defaultArrowMD ty bodyTy,
            mdty: getMDType topmd termPath, term: Lambda md tBind ty body bodyTy, termPath} md
        {ctxs, mdty: defaultMDType, tBind}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTypePath args {topmd, ctxs, ty, typePath: (Let3 md tBind@(TermBind xmd x) tyBinds def {-Type-} body bodyTy) : termPath} =
    let ctxs' = ctxs{ctx = insert x (tyBindsWrapType tyBinds ty) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
    args.let3 {topmd, ctxs, ty: bodyTy, mdty: getMDType topmd termPath, term: Let md tBind tyBinds def ty body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType{indented= md.varIndented}, tBind}
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType{indented= md.defIndented}, ty: ty, term: def}
        {ctxs: ctxs', mdty: defaultMDType{indented= md.bodyIndented}, ty: bodyTy, term: body} bodyTy
recTypePath args {topmd, ctxs, ty, typePath: (TLet3 md tyBind@(TypeBind _ x) tyBinds {-Type-} body bodyTy) : termPath} =
    let ctxs' = ctxs{kctx= delete x ctxs.kctx, mdkctx= delete x ctxs.mdkctx} in
    args.tLet3 {topmd, ctxs: ctxs', mdty: getMDType topmd termPath, ty: bodyTy, term: TLet md tyBind tyBinds ty body bodyTy, termPath}
        md {ctxs: ctxs', mdty: defaultMDType, tyBind}
        {ctxs: ctxs', mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypePath args {topmd, ctxs, ty, typePath: (Buffer2 md def {-Type-} body bodyTy) : termPath} =
    args.buffer2 {topmd, ctxs, mdty: getMDType topmd termPath, ty: bodyTy, term: Buffer md def ty body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType, ty, term: def}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypePath args {topmd, ctxs, ty, typePath: (CtrParam1 md {-Type-}) : ctrParamPath} =
    args.ctrParam1 {topmd, ctxs, mdty: getMDType topmd ctrParamPath, ctrParam: CtrParam md ty, ctrParamPath} md
recTypePath args {topmd, ctxs, ty, typePath: (TypeArg1 md {-Type-}) : typeArgPath} =
    args.typeArg1 {topmd, ctxs, mdty: getMDType topmd typeArgPath, tyArg: TypeArg md ty, typeArgPath} md
recTypePath args {topmd, ctxs, ty, typePath: (Arrow1 md {-Type-} t2) : typePath} =
    args.arrow1 {topmd, ctxs, mdty: getMDType topmd typePath, ty: Arrow md ty t2, typePath} md
        {ctxs, mdty: defaultMDType{indented= md.codIndented}, ty: t2}
recTypePath args {topmd, ctxs, ty, typePath: (Arrow2 md t1 {-Type-}) : typePath} =
    args.arrow2 {topmd, ctxs, mdty: getMDType topmd typePath, ty: Arrow md t1 ty, typePath} md
        {ctxs, mdty: defaultMDType, ty: t1}
recTypePath _ _ = unsafeThrow "Either wasn't a TypePath or I forgot a case!"

type CtrPathRec a = {
    ctrListCons1 :: ListCtrPathRecValue -> ListCtrRecValue -> a
}

recCtrPath :: forall a. CtrPathRec a -> CtrPathRecValue -> a
recCtrPath args {ctxs, ctr, topmd, ctrPath: (CtrListCons1 {-Constructor-} ctrs) : listCtrPath} =
    args.ctrListCons1 {topmd, ctxs, mdty: getMDType topmd listCtrPath, ctrs: ctr : ctrs, listCtrPath}
        {ctxs, mdty: defaultMDType, ctrs}
recCtrPath _ _ = unsafeThrow "Either wasn't a CtrPath or I forgot a case"

type TypeArgPathRec a = {
    typeArgListCons1 :: ListTypeArgPathRecValue -> ListTypeArgRecValue -> a
}

recTypeArgPath :: forall a. TypeArgPathRec a -> TypeArgPathRecValue -> a
recTypeArgPath args {topmd, ctxs, tyArg, typeArgPath: (TypeArgListCons1 tyArgs) : listTypeArgPath} =
    args.typeArgListCons1 {topmd, ctxs, mdty: getMDType topmd listTypeArgPath, tyArgs: (tyArg : tyArgs), listTypeArgPath}
        {ctxs, mdty: defaultMDType, tyArgs}
recTypeArgPath _ _ = unsafeThrow "Either wasn't a TypeArgPath or I forgot a case"

type TypeBindPathRec a = {
    tLet1 :: TermPathRecValue -> TLetMD -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , data1 :: TermPathRecValue -> GADTMD -> ListTypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a
    , typeBindListCons1 :: ListTypeBindPathRecValue -> ListTypeBindRecValue -> a
}

recTypeBindPath :: forall a. TypeBindPathRec a -> TypeBindPathRecValue -> a
recTypeBindPath args {topmd, ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (TLet1 md {-TypeBind-} tyBinds def body bodyTy) : termPath} =
    let ctxs' = ctxs{kctx = insert x (bindsToKind tyBinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx} in
    args.tLet1 {topmd, ctxs, mdty: getMDType topmd termPath, ty: bodyTy, term: TLet md tyBind tyBinds def body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: def}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypeBindPath args {topmd, ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (Data1 md {-TypeBind-} tyBinds ctrs body bodyTy) : termPath} =
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.data1 {topmd, ctxs, mdty: getMDType topmd termPath, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath} md
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ctrs}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypeBindPath args {topmd, ctxs, tyBind, typeBindPath: (TypeBindListCons1 tyBinds) : listTypeBindPath} =
    args.typeBindListCons1 {topmd, ctxs, mdty: getMDType topmd listTypeBindPath, tyBinds: (tyBind : tyBinds), listTypeBindPath}
        {ctxs, mdty: defaultMDType, tyBinds}
recTypeBindPath _ _ = unsafeThrow "Either wasn't a TypeBindPath or I forgot a case"

type TermBindPathRec a = {
    lambda1 :: TermPathRecValue -> LambdaMD -> TypeRecValue -> TermRecValue -> Type -> a
    , let1 :: TermPathRecValue -> LetMD -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , constructor1 :: CtrPathRecValue -> CtrMD -> ListCtrParamRecValue -> a
}

recTermBindPath :: forall a. TermBindPathRec a -> TermBindPathRecValue -> a
recTermBindPath args {topmd, ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Lambda1 md {-TermBind-} argTy body bodyTy) : termPath} =
    let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType argTy) ctxs.ctx} in
    args.lambda1
        {topmd, ctxs, mdty: getMDType topmd termPath, ty: (Arrow defaultArrowMD argTy bodyTy), term: (Lambda md tBind argTy body bodyTy), termPath} md
        {ctxs, mdty: defaultMDType, ty: argTy}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTermBindPath args {topmd, ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Let1 md {-TermBind-} tyBinds def defTy body bodyTy) : termPath} =
    let ctxs' = ctxs{ctx = insert x (tyBindsWrapType tyBinds defTy) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
    args.let1 {topmd, ctxs, mdty: getMDType topmd termPath, ty: bodyTy, term: (Let md tBind tyBinds def defTy body bodyTy), termPath} md
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy, term: def}
        {ctxs, mdty: defaultMDType, ty: defTy}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTermBindPath args {topmd, ctxs, tBind, termBindPath: (Constructor1 md {-TermBind-} ctrParams) : ctrPath} =
    args.constructor1 {topmd, ctxs, mdty: getMDType topmd ctrPath, ctr: Constructor md tBind ctrParams, ctrPath}
        md {ctxs, mdty: defaultMDType, ctrParams}
recTermBindPath _ _ = unsafeThrow "Either wasn't a TermBindPath or I forgot a case"

type ListCtrPathRec a = {
    data3 :: TermPathRecValue -> GADTMD -> TypeBindRecValue -> ListTypeBindRecValue -> TermRecValue -> Type -> a
    , ctrListCons2 :: ListCtrPathRecValue -> CtrRecValue -> a
}

recListCtrPath :: forall a . ListCtrPathRec a -> ListCtrPathRecValue -> a
recListCtrPath args {topmd, ctxs, ctrs, listCtrPath: (Data3 md tyBind tyBinds {-List Constructor-} body bodyTy : termPath)} =
    let ctxs' = removeDataFromCtx ctxs tyBind tyBinds ctrs in
    args.data3 {topmd, ctxs: ctxs', mdty: getMDType topmd termPath, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath}
        md {ctxs: ctxs', mdty: defaultMDType, tyBind}
        {ctxs: ctxs', mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recListCtrPath args {topmd, ctxs, ctrs, listCtrPath: (CtrListCons2 ctr {-List Constructor-} : listCtrPath)} =
    args.ctrListCons2 {topmd, ctxs, mdty: getMDType topmd listCtrPath, ctrs: ctr: ctrs, listCtrPath}
        {ctxs, mdty: defaultMDType, ctr}
recListCtrPath _ _ = unsafeThrow "Either wasn't a ListCtrPath or I forgot a case"

type ListCtrParamPathRec a = {
    constructor2 :: CtrPathRecValue -> CtrMD -> TermBindRecValue -> a
    , ctrParamListCons2 :: ListCtrParamPathRecValue -> CtrParamRecValue -> a
}

recListCtrParamPath :: forall a. ListCtrParamPathRec a -> ListCtrParamPathRecValue -> a
recListCtrParamPath args {topmd, ctxs, ctrParams, listCtrParamPath : Constructor2 md tBind {-List CtrParam-} : ctrPath} =
    args.constructor2 {topmd, ctxs, mdty: getMDType topmd ctrPath, ctr: Constructor md tBind ctrParams, ctrPath}
        md {ctxs, mdty: defaultMDType, tBind}
recListCtrParamPath args {topmd, ctxs, ctrParams, listCtrParamPath : CtrParamListCons2 ctrParam {-List CtrParam-} : listCtrParamPath} =
    args.ctrParamListCons2 {topmd, ctxs, mdty: getMDType topmd listCtrParamPath, ctrParams: ctrParam : ctrParams, listCtrParamPath}
        {ctxs, mdty: defaultMDType, ctrParam}
recListCtrParamPath _ _ = unsafeThrow "Either wasn't a ListCtrParamPath or I forgot a case"

type ListTypeArgPathRec a = {
    tNeu1 :: TypePathRecValue -> TNeuMD -> TypeVarID -> a
    , typeArgListCons2 :: ListTypeArgPathRecValue -> TypeArgRecValue -> a
}

recListTypeArgPath :: forall a. ListTypeArgPathRec a -> ListTypeArgPathRecValue -> a
recListTypeArgPath args {topmd, ctxs, tyArgs, listTypeArgPath: TNeu1 md x {-List TypeArg-} : typePath} =
    args.tNeu1 {topmd, ctxs, mdty: getMDType topmd typePath, ty: TNeu md x tyArgs, typePath}
        md x
recListTypeArgPath args {topmd, ctxs, tyArgs, listTypeArgPath: TypeArgListCons2 tyArg {-List TypeArg-} : listTypeArgPath} =
    args.typeArgListCons2 {topmd, ctxs, mdty: getMDType topmd listTypeArgPath, tyArgs: tyArg : tyArgs, listTypeArgPath}
        {ctxs, mdty: defaultMDType, tyArg}
recListTypeArgPath _ _ = unsafeThrow "Either wasn't a ListTypeArgPath or I forgot a case"

type ListTypeBindPathRec a = {
    data2 :: TermPathRecValue -> GADTMD -> TypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a
    , tLet2 :: TermPathRecValue -> TLetMD -> TypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , typeBindListCons2 :: ListTypeBindPathRecValue -> TypeBindRecValue -> a
}

recListTypeBindPath :: forall a . ListTypeBindPathRec a -> ListTypeBindPathRecValue -> a
recListTypeBindPath args {topmd, ctxs, tyBinds, listTypeBindPath: Data2 md tyBind ctrs body bodyTy : termPath} =
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.data2 {topmd, ctxs, mdty: getMDType topmd termPath, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType, tyBind}
        {ctxs: ctxs', mdty: defaultMDType, ctrs}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recListTypeBindPath _ _ = unsafeThrow "Either wasn't a ListTypeArgPath or I forgot a case"

-- List TypeBind
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    TypeBindListCons2 (TypeBind) {-List TypeBind-}

{-
List of things worth double checking, because they would lead to confusing bugs:
- properly handling contexts
    - everywhere the right things need to be added or removed from the contexts in each returned *RecValue
- properly building inner term
    - *PathRec keeps track of the term that was inside the path. This needs to be correctly built.

The idea is that when I wrote the code I looked at adjacent cases next to each other, so when proofreading I should look
at adjacent concepts next to each other instead.
-}