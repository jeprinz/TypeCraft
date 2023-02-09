module TypeCraft.Purescript.PathRec where

import Prelude
import Prim hiding (Type)
import Data.Map.Internal (insert)

import TypeCraft.Purescript.Grammar (Change, Constructor(..), CtrParam(..), PolyType(..), Term(..), TermBind(..), TermVarID, Tooth(..), Type(..), TypeArg(..), TypeBind(..), TypeVarID, UpPath, VarChange)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCtxVarChange, invertVarChange)
import TypeCraft.Purescript.MD
import Data.List (List, (:))
import TypeCraft.Purescript.Context (AllContext, addDataToCtx, removeDataFromCtx, tyBindsWrapType)
import TypeCraft.Purescript.TermRec (CtrParamRecValue, CtrRecValue, ListCtrParamRecValue, ListCtrRecValue, ListTypeArgRecValue, ListTypeBindRecValue, TermBindRecValue, TermRecValue, TypeArgRecValue, TypeBindRecValue, TypeRecValue)
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Context (addLetToCtx)
import TypeCraft.Purescript.Util (delete')
import Data.Tuple (fst, snd)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints)
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Alpha (polyTypeApply)
import Debug (trace)

type TermPathRecValue = {ctxs :: AllContext, ty :: Type, term :: Term, termPath :: UpPath}
type TypePathRecValue = {ctxs :: AllContext, ty :: Type, typePath :: UpPath}
type CtrPathRecValue = {ctxs :: AllContext, ctr :: Constructor, ctrPath :: UpPath}
type CtrParamPathRecValue = {ctxs :: AllContext, ctrParam :: CtrParam, ctrParamPath :: UpPath}
type TypeArgPathRecValue = {ctxs :: AllContext, tyArg :: TypeArg, typeArgPath :: UpPath}
type TypeBindPathRecValue = {ctxs :: AllContext, tyBind :: TypeBind, typeBindPath :: UpPath}
type TermBindPathRecValue = {ctxs :: AllContext, tBind :: TermBind, termBindPath :: UpPath}
type ListCtrPathRecValue = {ctxs :: AllContext, ctrs :: List Constructor, listCtrPath :: UpPath}
type ListCtrParamPathRecValue = {ctxs :: AllContext, ctrParams :: List CtrParam, listCtrParamPath :: UpPath}
type ListTypeArgPathRecValue = {ctxs :: AllContext, tyArgs :: List TypeArg, listTypeArgPath :: UpPath}
type ListTypeBindPathRecValue = {ctxs :: AllContext, tyBinds :: List TypeBind, listTypeBindPath :: UpPath}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let4), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let3 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , let5 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> Type -> a
    , app1 :: TermPathRecValue -> AppMD -> TermRecValue -> Type -> Type -> a
    , app2 :: TermPathRecValue -> AppMD -> TermRecValue -> Type -> Type -> a
    , lambda3 :: TermPathRecValue -> LambdaMD -> TermBindRecValue -> TypeRecValue -> Type -> a
    , buffer1 :: TermPathRecValue -> BufferMD -> TypeRecValue -> TermRecValue -> Type -> a
    , buffer3 :: TermPathRecValue -> BufferMD -> TermRecValue -> TypeRecValue -> Type -> a
    , typeBoundary1 :: TermPathRecValue -> TypeBoundaryMD -> Change -> a
    , contextBoundary1 :: TermPathRecValue -> ContextBoundaryMD -> TermVarID -> VarChange -> a
    , tLet4 :: TermPathRecValue -> TLetMD -> TypeBind -> ListTypeBindRecValue -> TypeRecValue -> Type -> a
    , data4 :: TermPathRecValue -> GADTMD -> TypeBindRecValue -> ListTypeBindRecValue -> ListCtrRecValue -> Type -> a
}

recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {ctxs, ty, term, termPath: (Let3 md tBind@(TermBind xmd x) tyBinds {-Term-} defTy body bodyTy) : up} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected 1" else
    let ctxs' = ctxs{mdctx = delete' x ctxs.mdctx, ctx = delete' x ctxs.ctx} in
    let ctxs'' = removeLetTypeFromCtx ctxs' tyBinds in
    args.let3 {ctxs: ctxs'', ty: bodyTy, term: Let md tBind tyBinds term defTy body bodyTy, termPath: up} md
        {ctxs: ctxs'', tBind} {ctxs: ctxs'', tyBinds}
        {ctxs: ctxs', ty: defTy}
        {ctxs, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, term, termPath: (Let5 md tBind@(TermBind _ x) tyBinds def defTy {-Term-} bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdctx = delete' x ctxs.mdctx, ctx = delete' x ctxs.ctx} in
    let ctxs'' = removeLetTypeFromCtx ctxs' tyBinds in
    args.let5 {ctxs: ctxs'', ty: ty, term: (Let md tBind tyBinds def defTy term bodyTy), termPath: up} md
        {ctxs: ctxs'', tBind} {ctxs: ctxs', tyBinds}
        {ctxs, ty: defTy, term: def} --def
        {ctxs: ctxs', ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, term, termPath: (App1 md {-Term-} t2 argTy outTy) : up} =
    if not (Arrow defaultArrowMD argTy outTy == ty) then unsafeThrow "dynamic type error detected 2" else
    args.app1 {ctxs, ty: outTy, term: App md term t2 argTy outTy, termPath: up} md
        {ctxs, ty: argTy, term: t2}
        argTy outTy
recTermPath args {ctxs, ty, term, termPath: (App2 md t1 {-Term-} argTy outTy) : up} =
    if not (argTy == ty) then unsafeThrow "dynamic type error detected 3" else
    args.app2 {ctxs, ty: outTy, term: App md t1 term argTy outTy, termPath: up} md
        {ctxs, ty: Arrow defaultArrowMD argTy outTy, term: t1}
        argTy outTy
recTermPath args {ctxs, ty, term, termPath: (Lambda3 md tBind@(TermBind _ x) argTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected 4" else
    let ctxs' = ctxs{mdctx= delete' x ctxs.mdctx, ctx= delete' x ctxs.ctx} in
    args.lambda3 {ctxs: ctxs', ty: Arrow defaultArrowMD argTy bodyTy, term: Lambda md tBind argTy term bodyTy, termPath: up}
        md {ctxs, tBind} {ctxs: ctxs', ty: argTy}
        bodyTy
recTermPath args {ctxs, ty, term, termPath: (Buffer1 md {-Term-} bufTy body bodyTy) : up} =
    if not (bufTy == ty) then unsafeThrow "dynamic type error detected 5" else
    args.buffer1 {ctxs, ty: bodyTy, term: Buffer md term bufTy body bodyTy, termPath: up}
        md {ctxs, ty: bufTy}
        {ctxs, ty: bodyTy, term: body}
        bodyTy
recTermPath args {ctxs, ty, term, termPath: (Buffer3 md buf bufTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected 6" else
    args.buffer3 {ctxs, ty: bodyTy, term: Buffer md buf bufTy term bodyTy, termPath: up}
        md {ctxs, ty: bufTy, term: buf}
        {ctxs, ty: bufTy} bodyTy
recTermPath args {ctxs, ty, term, termPath: (TypeBoundary1 md c {-Term-}) : up} =
    if not (ty == fst (getEndpoints c)) then unsafeThrow ("shouldn't happen recTerm typebound. c is: " <> show c <> "and ty is: " <> show ty) else
    args.typeBoundary1 {ctxs, ty: (snd (getEndpoints c)), term: TypeBoundary md c term, termPath: up} md c
recTermPath args {ctxs, ty, term, termPath: (ContextBoundary1 md x c) : up} =
    let ctxs' = ctxs{ctx = alterCtxVarChange ctxs.ctx x (invertVarChange c)} in
    args.contextBoundary1 {ctxs: ctxs', ty: ty, term: ContextBoundary md x c term, termPath: up} md x c
recTermPath args {ctxs, ty, term, termPath: (TLet4 md tyBind@(TypeBind _ x) tyBinds def {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected 7" else
    let ctxs' = removeTLetFromCtx ctxs tyBind in
    args.tLet4 {ctxs: ctxs', ty: bodyTy, term: TLet md tyBind tyBinds def term bodyTy, termPath: up}
        md tyBind {ctxs, tyBinds} {ctxs: ctxs', ty: def} bodyTy
recTermPath args {ctxs, ty, term, termPath: (Data4 md tyBind@(TypeBind _ x) tyBinds ctrs {-Term-} bodyTy) : up} =
    let ctxs' = removeDataFromCtx ctxs tyBind tyBinds ctrs in
    args.data4 {ctxs: ctxs', ty: bodyTy, term: Data md tyBind tyBinds ctrs term bodyTy, termPath: up}
        md {ctxs: ctxs', tyBind} {ctxs: ctxs', tyBinds}
        {ctxs, ctrs} bodyTy
recTermPath _ _ = unsafeThrow "recTermPath given something that isn't a term path"

type TypePathRec a = {
      lambda2 :: TermPathRecValue -> LambdaMD -> TermBindRecValue -> TermRecValue -> Type -> a
      , let4 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TermRecValue -> Type -> a
      , buffer2 :: TermPathRecValue -> BufferMD -> TermRecValue -> TermRecValue -> Type -> a
      , tLet3 :: TermPathRecValue -> TLetMD -> TypeBindRecValue -> ListTypeBindRecValue -> TermRecValue -> Type -> a
      , ctrParam1 :: CtrParamPathRecValue -> CtrParamMD -> a
      , typeArg1 :: TypeArgPathRecValue -> TypeArgMD -> a
      , arrow1 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
      , arrow2 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
}

recTypePath :: forall a. TypePathRec a -> TypePathRecValue -> a
recTypePath args {ctxs, ty, typePath: (Lambda2 md tBind@(TermBind xmd x) {-Type-} body bodyTy) : termPath} =
  let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType ty) ctxs.ctx} in
    args.lambda2 {ctxs, ty: Arrow defaultArrowMD ty bodyTy, term: Lambda md tBind ty body bodyTy, termPath} md
        {ctxs, tBind}
        {ctxs: ctxs', ty: bodyTy, term: body}
        bodyTy
recTypePath args {ctxs, ty, typePath: (Let4 md tBind@(TermBind xmd x) tyBinds def {-Type-} body bodyTy) : termPath} =
    let ctxs' = ctxs{ctx = insert x (tyBindsWrapType tyBinds ty) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
    let ctxsRemoved = removeLetTypeFromCtx ctxs tyBinds in
    args.let4 {ctxs, ty: bodyTy, term: Let md tBind tyBinds def ty body bodyTy, termPath}
        md {ctxs: ctxsRemoved, tBind}
        {ctxs: ctxsRemoved, tyBinds}
        {ctxs: ctxs', ty: ty, term: def}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (TLet3 md tyBind@(TypeBind _ x) tyBinds {-Type-} body bodyTy) : termPath} =
    let ctxs' = addTLetToCtx ctxs tyBind tyBinds ty in
    args.tLet3 {ctxs: ctxs', ty: bodyTy, term: TLet md tyBind tyBinds ty body bodyTy, termPath}
        md {ctxs: ctxs', tyBind}
        {ctxs: ctxs', tyBinds}
        {ctxs, ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (Buffer2 md def {-Type-} body bodyTy) : termPath} =
    args.buffer2 {ctxs, ty: bodyTy, term: Buffer md def ty body bodyTy, termPath}
        md {ctxs, ty, term: def}
        {ctxs, ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (CtrParam1 md {-Type-}) : ctrParamPath} =
    args.ctrParam1 {ctxs, ctrParam: CtrParam md ty, ctrParamPath} md
recTypePath args {ctxs, ty, typePath: (TypeArg1 md {-Type-}) : typeArgPath} =
    args.typeArg1 {ctxs, tyArg: TypeArg md ty, typeArgPath} md
recTypePath args {ctxs, ty, typePath: (Arrow1 md {-Type-} t2) : typePath} =
    args.arrow1 {ctxs, ty: Arrow md ty t2, typePath} md
        {ctxs, ty: t2}
recTypePath args {ctxs, ty, typePath: (Arrow2 md t1 {-Type-}) : typePath} =
    args.arrow2 {ctxs, ty: Arrow md t1 ty, typePath} md
        {ctxs, ty: t1}
recTypePath _ _ = unsafeThrow "Either wasn't a TypePath or I forgot a case!"

type CtrPathRec a = {
    ctrListCons1 :: ListCtrPathRecValue -> ListCtrRecValue -> a
}

recCtrPath :: forall a. CtrPathRec a -> CtrPathRecValue -> a
recCtrPath args {ctxs, ctr, ctrPath: (CtrListCons1 {-Constructor-} ctrs) : listCtrPath} =
    args.ctrListCons1 {ctxs, ctrs: ctr : ctrs, listCtrPath}
        {ctxs, ctrs}
recCtrPath _ _ = unsafeThrow "Either wasn't a CtrPath or I forgot a case"

type CtrParamPathRec a = {
    ctrParamListCons1 :: ListCtrParamPathRecValue -> ListCtrParamRecValue -> a
}

recCtrParamPath :: forall a. CtrParamPathRec a -> CtrParamPathRecValue -> a
recCtrParamPath args {ctxs, ctrParam, ctrParamPath: (CtrParamListCons1 {-ConstructorParam-} ctrParams) : listCtrParamPath} =
    args.ctrParamListCons1 {ctxs, ctrParams: ctrParam : ctrParams, listCtrParamPath}
        {ctxs, ctrParams}
recCtrParamPath _ _ = unsafeThrow "Either wasn't a CtrPath or I forgot a case"

type TypeArgPathRec a = {
    typeArgListCons1 :: ListTypeArgPathRecValue -> ListTypeArgRecValue -> a
}

recTypeArgPath :: forall a. TypeArgPathRec a -> TypeArgPathRecValue -> a
recTypeArgPath args {ctxs, tyArg, typeArgPath: (TypeArgListCons1 tyArgs) : listTypeArgPath} =
    args.typeArgListCons1 {ctxs, tyArgs: (tyArg : tyArgs), listTypeArgPath}
        {ctxs, tyArgs}
recTypeArgPath _ _ = unsafeThrow "Either wasn't a TypeArgPath or I forgot a case"

type TypeBindPathRec a = {
    tLet1 :: TermPathRecValue -> TLetMD -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , data1 :: TermPathRecValue -> GADTMD -> ListTypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a
    , typeBindListCons1 :: ListTypeBindPathRecValue -> ListTypeBindRecValue -> a
}

recTypeBindPath :: forall a. TypeBindPathRec a -> TypeBindPathRecValue -> a
recTypeBindPath args {ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (TLet1 md {-TypeBind-} tyBinds def body bodyTy) : termPath} =
    let ctxs' = addTLetToCtx ctxs tyBind tyBinds def in
    args.tLet1 {ctxs, ty: bodyTy, term: TLet md tyBind tyBinds def body bodyTy, termPath}
        md {ctxs, tyBinds}
        {ctxs, ty: def}
        {ctxs, ty: bodyTy, term: body} bodyTy
recTypeBindPath args {ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (Data1 md {-TypeBind-} tyBinds ctrs body bodyTy) : termPath} =
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.data1 {ctxs, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath} md
        {ctxs, tyBinds}
        {ctxs: ctxs{kctx= ctxs'.kctx, mdkctx= ctxs'.mdkctx}, ctrs}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recTypeBindPath args {ctxs, tyBind, typeBindPath: (TypeBindListCons1 tyBinds) : listTypeBindPath} =
    args.typeBindListCons1 {ctxs, tyBinds: (tyBind : tyBinds), listTypeBindPath}
        {ctxs, tyBinds}
recTypeBindPath _ _ = unsafeThrow "Either wasn't a TypeBindPath or I forgot a case"

type TermBindPathRec a = {
    lambda1 :: TermPathRecValue -> LambdaMD -> TypeRecValue -> TermRecValue -> Type -> a
    , let1 :: TermPathRecValue -> LetMD -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , constructor1 :: CtrPathRecValue -> CtrMD -> ListCtrParamRecValue -> a
}

recTermBindPath :: forall a. TermBindPathRec a -> TermBindPathRecValue -> a
recTermBindPath args {ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Lambda1 md {-TermBind-} argTy body bodyTy) : termPath} =
    let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType argTy) ctxs.ctx} in
    args.lambda1
        {ctxs, ty: (Arrow defaultArrowMD argTy bodyTy), term: (Lambda md tBind argTy body bodyTy), termPath} md
        {ctxs, ty: argTy}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recTermBindPath args {ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Let1 md {-TermBind-} tyBinds def defTy body bodyTy) : termPath} =
    let ctxs' = addLetTypesToCtx (addLetToCtx ctxs tBind tyBinds defTy) tyBinds in
    args.let1 {ctxs, ty: bodyTy, term: (Let md tBind tyBinds def defTy body bodyTy), termPath} md
        {ctxs, tyBinds}
        {ctxs: ctxs', ty: defTy, term: def}
        {ctxs: addLetTypesToCtx ctxs tyBinds, ty: defTy}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recTermBindPath args {ctxs, tBind, termBindPath: (Constructor1 md {-TermBind-} ctrParams) : ctrPath} =
    args.constructor1 {ctxs, ctr: Constructor md tBind ctrParams, ctrPath}
        md {ctxs, ctrParams}
recTermBindPath args {ctxs, tBind, termBindPath}= unsafeThrow $ "Either wasn't a TermBindPath or I forgot a case; termBindPath = " <> show termBindPath

type ListCtrPathRec a = {
    data3 :: TermPathRecValue -> GADTMD -> TypeBindRecValue -> ListTypeBindRecValue -> TermRecValue -> Type -> a
    , ctrListCons2 :: ListCtrPathRecValue -> CtrRecValue -> a
}

recListCtrPath :: forall a . ListCtrPathRec a -> ListCtrPathRecValue -> a
recListCtrPath args {ctxs, ctrs, listCtrPath: (Data3 md tyBind tyBinds {-List Constructor-} body bodyTy : termPath)} =
    let ctxs' = removeDataFromCtx ctxs tyBind tyBinds ctrs in
    args.data3 {ctxs: ctxs', ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath}
        md {ctxs: ctxs', tyBind}
        {ctxs: ctxs', tyBinds}
        {ctxs: addDataToCtx ctxs tyBind tyBinds ctrs, ty: bodyTy, term: body} bodyTy
recListCtrPath args {ctxs, ctrs, listCtrPath: (CtrListCons2 ctr {-List Constructor-} : listCtrPath)} =
    args.ctrListCons2 {ctxs, ctrs: ctr: ctrs, listCtrPath}
        {ctxs, ctr}
recListCtrPath _ _ = unsafeThrow "Either wasn't a ListCtrPath or I forgot a case"

type ListCtrParamPathRec a = {
    constructor2 :: CtrPathRecValue -> CtrMD -> TermBindRecValue -> a
    , ctrParamListCons2 :: ListCtrParamPathRecValue -> CtrParamRecValue -> a
}

recListCtrParamPath :: forall a. ListCtrParamPathRec a -> ListCtrParamPathRecValue -> a
recListCtrParamPath args {ctxs, ctrParams, listCtrParamPath : Constructor2 md tBind {-List CtrParam-} : ctrPath} =
    args.constructor2 {ctxs, ctr: Constructor md tBind ctrParams, ctrPath}
        md {ctxs, tBind}
recListCtrParamPath args {ctxs, ctrParams, listCtrParamPath : CtrParamListCons2 ctrParam {-List CtrParam-} : listCtrParamPath} =
    args.ctrParamListCons2 {ctxs, ctrParams: ctrParam : ctrParams, listCtrParamPath}
        {ctxs, ctrParam}
recListCtrParamPath _ _ = unsafeThrow "Either wasn't a ListCtrParamPath or I forgot a case"

type ListTypeArgPathRec a = {
    tNeu1 :: TypePathRecValue -> TNeuMD -> TypeVarID -> a
    , typeArgListCons2 :: ListTypeArgPathRecValue -> TypeArgRecValue -> a
    , var1 :: TermPathRecValue -> VarMD -> TermVarID -> a
}

recListTypeArgPath :: forall a. ListTypeArgPathRec a -> ListTypeArgPathRecValue -> a
recListTypeArgPath args {ctxs, tyArgs, listTypeArgPath: TNeu1 md x {-List TypeArg-} : typePath} =
    args.tNeu1 {ctxs, ty: TNeu md x tyArgs, typePath}
        md x
recListTypeArgPath args {ctxs, tyArgs, listTypeArgPath: Var1 md x {-List TypeArg-} : termPath} =
    args.var1 {ctxs, ty: polyTypeApply (lookup' x ctxs.ctx) tyArgs, term: Var md x tyArgs , termPath}
        md x
recListTypeArgPath args {ctxs, tyArgs, listTypeArgPath: TypeArgListCons2 tyArg {-List TypeArg-} : listTypeArgPath} =
    args.typeArgListCons2 {ctxs, tyArgs: tyArg : tyArgs, listTypeArgPath}
        {ctxs, tyArg}
recListTypeArgPath _ _ = unsafeThrow "Either wasn't a ListTypeArgPath or I forgot a case"

type ListTypeBindPathRec a = {
    data2 :: TermPathRecValue -> GADTMD -> TypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a
    , tLet2 :: TermPathRecValue -> TLetMD -> TypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , typeBindListCons2 :: ListTypeBindPathRecValue -> TypeBindRecValue -> a
    , let2 :: TermPathRecValue -> LetMD -> TermBindRecValue -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
}

recListTypeBindPath :: forall a . ListTypeBindPathRec a -> ListTypeBindPathRecValue -> a
recListTypeBindPath args {ctxs, tyBinds, listTypeBindPath: Data2 md tyBind ctrs body bodyTy : termPath} =
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.data2 {ctxs, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath}
        md {ctxs, tyBind}
        {ctxs: ctxs{kctx= ctxs'.kctx, mdkctx= ctxs'.mdkctx}, ctrs}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recListTypeBindPath args {ctxs, tyBinds, listTypeBindPath: TLet2 md tyBind {-List TypeBind-} def body bodyTy : termPath} =
    let ctxs' = addTLetToCtx ctxs tyBind tyBinds def in
    args.tLet2 {ctxs, ty: bodyTy, term: TLet md tyBind tyBinds def body bodyTy, termPath}
        md {ctxs, tyBind}
        {ctxs, ty: def}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recListTypeBindPath args {ctxs, tyBinds, listTypeBindPath: Let2 md tBind {-List TypeBind-} def defTy body bodyTy : termPath} =
    let ctxs' = addLetTypesToCtx (addLetToCtx ctxs tBind tyBinds defTy) tyBinds in
    args.let2 {ctxs, ty: bodyTy, term: Let md tBind tyBinds def defTy body bodyTy, termPath}
        md {ctxs, tBind} {ctxs: ctxs', ty: defTy, term: def}
        {ctxs: addLetTypesToCtx ctxs tyBinds, ty: defTy}
        {ctxs: ctxs', ty: bodyTy, term: body} bodyTy
recListTypeBindPath args {ctxs, tyBinds, listTypeBindPath: TypeBindListCons2 tyBind {-List TypeBind-} : listTypeBindPath} =
    args.typeBindListCons2 {ctxs, tyBinds: tyBind : tyBinds, listTypeBindPath}
        {ctxs, tyBind}
recListTypeBindPath _ listTypeBindPath = unsafeThrow ("Either wasn't a ListTypeBindPath or I forgot a case. path is: " <> show listTypeBindPath.listTypeBindPath)

-- List TypeBind
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    Let2 LetMD TermBind {-List TypeBind-} Term Type Term Type
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