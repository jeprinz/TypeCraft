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
import TypeCraft.Purescript.Substitution (Sub, combineSub, subChange, subChangeCtx, unify)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import Data.Tuple (fst)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermRec
import Data.Set (member)
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Kinds (bindsToKind)

type TermPathRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, term :: Term, termPath :: UpPath}
type TypePathRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, typePath :: UpPath}
type CtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctr :: Constructor, ctrPath :: UpPath}
type CtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctrParam :: CtrParam, ctrParamPath :: UpPath}
type TypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, tyArg :: TypeArg, typeArgPath :: UpPath}
type TypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, tyBind :: TypeBind, typeBindPath :: UpPath}
type TermBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, tBind :: TermBind, termBindPath :: UpPath}
type ListCtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctrs :: List Constructor, listCtrPath :: UpPath}
type ListCtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctrParams :: List CtrParam, listCtrParamPath :: UpPath}
type ListTypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, tyArgs :: List TypeArg, listTypeArgPath :: UpPath}
type ListTypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, tyBinds :: List TypeBind, listTypeBindPath :: UpPath}
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
    , contextBoundary1 :: TermPathRecValue -> ContextBoundaryMD -> TermVarID -> Change -> a
    , tLet4 :: TermPathRecValue -> TLetMD -> TypeBind -> ListTypeBindRecValue -> TypeRecValue -> Type -> a
    , data4 :: TermPathRecValue -> GADTMD -> TypeBind -> ListTypeBindRecValue -> ListCtrRecValue -> Type -> a
}

-- TODO: need to get indentation!
getMDType :: UpPath -> MDType
getMDType (App1 _ _ _ _ : _ : _) = defaultMDType{onLeftOfApp = true}
getMDType (App2 _ _ _ _ : _ : _) = defaultMDType{onRightOfApp = true}
getMDType (Arrow1 _ _ : _ : _) = defaultMDType{onLeftOfArrow = true}
getMDType _ = defaultMDType

getParentMDType :: UpPath -> MDType
getParentMDType (_ : teeth) = getMDType teeth
getParentMDType _ = defaultMDType

recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {ctxs, ty, term, termPath: (Let2 md tBind@(TermBind xmd x) tyBinds {-Term-} defTy body bodyTy) : up} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let2 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, term: Let md tBind tyBinds term defTy body bodyTy, termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, term, termPath: (Let4 md tBind@(TermBind _ x) tyBinds def defTy {-Term-} bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let4 {ctxs: ctxs', mdty: getMDType up, ty: ty, term: (Let md tBind tyBinds def defTy term bodyTy), termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: defTy, term: def} --def
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, term, termPath: (App1 md {-Term-} t2 argTy outTy) : up} =
    if not (Arrow defaultArrowMD argTy outTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app1 {ctxs, mdty: getMDType up, ty: outTy, term: App md term t2 argTy outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onRightOfApp= true}, ty: argTy, term: t2}
        argTy outTy
recTermPath args {ctxs, ty, term, termPath: (App2 md t1 {-Term-} argTy outTy) : up} =
    if not (argTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app2 {ctxs, mdty: getMDType up, ty: outTy, term: App md t1 term argTy outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onLeftOfApp= true}, ty: Arrow defaultArrowMD argTy outTy, term: t1}
        argTy outTy
recTermPath args {ctxs, ty, term, termPath: (Lambda3 md tbind@(TermBind _ x) argTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx= delete x ctxs.mdctx, ctx= delete x ctxs.ctx} in
    args.lambda3 {ctxs: ctxs', mdty: getMDType up, ty: Arrow defaultArrowMD argTy bodyTy, term: Lambda md tbind argTy term bodyTy, termPath: up}
        md tbind {ctxs: ctxs', mdty: defaultMDType, ty: argTy}
        bodyTy
recTermPath args {ctxs, ty, term, termPath: (Buffer1 md {-Term-} bufTy body bodyTy) : up} =
    if not (bufTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer1 {ctxs, mdty: getMDType up, ty: bodyTy, term: Buffer md term bufTy body bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTermPath args {ctxs, ty, term, termPath: (Buffer3 md buf bufTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer3 {ctxs, mdty: getMDType up, ty: bodyTy, term: Buffer md buf bufTy term bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy, term: buf}
        {ctxs, mdty: defaultMDType, ty: bufTy} bodyTy
recTermPath args {ctxs, ty, term, termPath: (TypeBoundary1 md c {-Term-}) : up} =
    args.typeBoundary1 {ctxs, mdty: getMDType up, ty: ty, term: TypeBoundary md c term, termPath: up} md c
recTermPath args {ctxs, ty, term, termPath: (ContextBoundary1 md x c) : up} =
    args.contextBoundary1 {ctxs, mdty: getMDType up, ty: ty, term: ContextBoundary md x c term, termPath: up} md x c
recTermPath args {ctxs, ty, term, termPath: (TLet4 md tybind@(TypeBind _ x) tyBinds def {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs {mdkctx = delete x ctxs.mdkctx, kctx = delete x ctxs.kctx} in
    args.tLet4 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, term: TLet md tybind tyBinds def term bodyTy, termPath: up}
        md tybind {ctxs, mdty: defaultMDType, tyBinds} {ctxs: ctxs', mdty: defaultMDType, ty: def} bodyTy
recTermPath args {ctxs, ty, term, termPath: (Data4 md tyBind@(TypeBind _ x) tyBinds ctrs {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctrIds = constructorIds ctrs in
    let ctxs' = ctxs {mdkctx = delete x ctxs.mdkctx, kctx = delete x ctxs.kctx
            ,ctx = filterKeys (\x -> not (member x ctrIds)) ctxs.ctx
            ,mdctx = filterKeys (\x -> not (member x ctrIds)) ctxs.mdctx} in
    args.data4 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, term: Data md tyBind tyBinds ctrs term bodyTy, termPath: up}
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
recTypePath args {ctxs, ty, typePath: (Lambda2 md tBind@(TermBind xmd x) {-Type-} body bodyTy) : termPath} =
  let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x ty ctxs.ctx} in
    args.lambda2 {ctxs, ty: Arrow defaultArrowMD ty bodyTy,
            mdty: getMDType termPath, term: Lambda md tBind ty body bodyTy, termPath} md
        {ctxs, mdty: defaultMDType, tBind}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTypePath args {ctxs, ty, typePath: (Let3 md tBind@(TermBind xmd x) tyBinds def {-Type-} body bodyTy) : termPath} =
    let ctxs' = ctxs{ctx = insert x ty ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
    args.let3 {ctxs, ty: bodyTy, mdty: getMDType termPath, term: Let md tBind tyBinds def ty body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType{indented= md.varIndented}, tBind}
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType{indented= md.defIndented}, ty: ty, term: def}
        {ctxs: ctxs', mdty: defaultMDType{indented= md.bodyIndented}, ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (TLet3 md tyBind@(TypeBind _ x) tyBinds {-Type-} body bodyTy) : termPath} =
    let ctxs' = ctxs{kctx= delete x ctxs.kctx, mdkctx= delete x ctxs.mdkctx} in
    args.tLet3 {ctxs: ctxs', mdty: getMDType termPath, ty: bodyTy, term: TLet md tyBind tyBinds ty body bodyTy, termPath}
        md {ctxs: ctxs', mdty: defaultMDType, tyBind}
        {ctxs: ctxs', mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (Buffer2 md def {-Type-} body bodyTy) : termPath} =
    args.buffer2 {ctxs, mdty: getMDType termPath, ty: bodyTy, term: Buffer md def ty body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType, ty, term: def}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypePath args {ctxs, ty, typePath: (CtrParam1 md {-Type-}) : ctrParamPath} =
    args.ctrParam1 {ctxs, mdty: getMDType ctrParamPath, ctrParam: CtrParam md ty, ctrParamPath} md
recTypePath args {ctxs, ty, typePath: (TypeArg1 md {-Type-}) : typeArgPath} =
    args.typeArg1 {ctxs, mdty: getMDType typeArgPath, tyArg: TypeArg md ty, typeArgPath} md
recTypePath args {ctxs, ty, typePath: (Arrow1 md {-Type-} t2) : typePath} =
    args.arrow1 {ctxs, mdty: getMDType typePath, ty: Arrow md ty t2, typePath} md
        {ctxs, mdty: defaultMDType{indented= md.codIndented}, ty: t2}
recTypePath args {ctxs, ty, typePath: (Arrow2 md t1 {-Type-}) : typePath} =
    args.arrow2 {ctxs, mdty: getMDType typePath, ty: Arrow md t1 ty, typePath} md
        {ctxs, mdty: defaultMDType, ty: t1}
recTypePath _ _ = unsafeThrow "Either wasn't a TypePath or I forgot a case!"

type CtrPathRec a = {
    ctrListCons1 :: ListCtrPathRecValue -> ListCtrRecValue -> a
}

recCtrPath :: forall a. CtrPathRec a -> CtrPathRecValue -> a
recCtrPath args {ctxs, ctr, ctrPath: (CtrListCons1 {-Constructor-} ctrs) : listCtrPath} =
    args.ctrListCons1 {ctxs, mdty: getMDType listCtrPath, ctrs: ctr : ctrs, listCtrPath}
        {ctxs, mdty: defaultMDType, ctrs}
recCtrPath _ _ = unsafeThrow "Either wasn't a CtrPath or I forgot a case"

type TypeArgPathRec a = {
    typeArgListCons1 :: ListTypeArgPathRecValue -> ListTypeArgRecValue -> a
}

recTypeArgPath :: forall a. TypeArgPathRec a -> TypeArgPathRecValue -> a
recTypeArgPath args {ctxs, tyArg, typeArgPath: (TypeArgListCons1 tyArgs) : listTypeArgPath} =
    args.typeArgListCons1 {ctxs, mdty: getMDType listTypeArgPath, tyArgs: (tyArg : tyArgs), listTypeArgPath}
        {ctxs, mdty: defaultMDType, tyArgs}
recTypeArgPath _ _ = unsafeThrow "Either wasn't a TypeArgPath or I forgot a case"

type TypeBindPathRec a = {
    tLet1 :: TermPathRecValue -> TLetMD -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , data1 :: TermPathRecValue -> GADTMD -> ListTypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a
    , typeBindListCons1 :: ListTypeBindPathRecValue -> ListTypeBindRecValue -> a
}

recTypeBindPath :: forall a. TypeBindPathRec a -> TypeBindPathRecValue -> a
recTypeBindPath args {ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (TLet1 md {-TypeBind-} tyBinds def body bodyTy) : termPath} =
    let ctxs' = ctxs{kctx = insert x (bindsToKind tyBinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx} in
    args.tLet1 {ctxs, mdty: getMDType termPath, ty: bodyTy, term: TLet md tyBind tyBinds def body bodyTy, termPath}
        md {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: def}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypeBindPath args {ctxs, tyBind: tyBind@(TypeBind xmd x), typeBindPath: (Data1 md {-TypeBind-} tyBinds ctrs body bodyTy) : termPath} =
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    let ctxs' = ctxs{kctx = insert x (bindsToKind tyBinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx
        , ctx= union ctxs.ctx (constructorTypes dataType ctrs)
        , mdctx= union ctxs.mdctx (constructorNames ctrs)} in
    args.data1 {ctxs, mdty: getMDType termPath, ty: bodyTy, term: Data md tyBind tyBinds ctrs body bodyTy, termPath} md
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ctrs}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTypeBindPath args {ctxs, tyBind, typeBindPath: (TypeBindListCons1 tyBinds) : listTypeBindPath} =
    args.typeBindListCons1 {ctxs, mdty: getMDType listTypeBindPath, tyBinds: (tyBind : tyBinds), listTypeBindPath}
        {ctxs, mdty: defaultMDType, tyBinds}
recTypeBindPath _ _ = unsafeThrow "Either wasn't a TypeBindPath or I forgot a case"

type TermBindPathRec a = {
    lambda1 :: TermPathRecValue -> LambdaMD -> TypeRecValue -> TermRecValue -> Type -> a
    , let1 :: TermPathRecValue -> LetMD -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , constructor1 :: CtrPathRecValue -> CtrMD -> ListCtrParamRecValue -> a
}

recTermBindPath :: forall a. TermBindPathRec a -> TermBindPathRecValue -> a
recTermBindPath args {ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Lambda1 md {-TermBind-} argTy body bodyTy) : termPath} =
    let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x argTy ctxs.ctx} in
    args.lambda1
        {ctxs, mdty: getMDType termPath, ty: (Arrow defaultArrowMD argTy bodyTy), term: (Lambda md tBind argTy body bodyTy), termPath} md
        {ctxs, mdty: defaultMDType, ty: argTy}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTermBindPath args {ctxs, tBind: tBind@(TermBind xmd x), termBindPath: (Let1 md {-TermBind-} tyBinds def defTy body bodyTy) : termPath} =
    let ctxs' = ctxs{ctx = insert x defTy ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
    args.let1 {ctxs, mdty: getMDType termPath, ty: bodyTy, term: (Let md tBind tyBinds def defTy body bodyTy), termPath} md
        {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy, term: def}
        {ctxs, mdty: defaultMDType, ty: defTy}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body} bodyTy
recTermBindPath args {ctxs, tBind, termBindPath: (Constructor1 md {-TermBind-} ctrParams) : ctrPath} =
    args.constructor1 {ctxs, mdty: getMDType ctrPath, ctr: Constructor md tBind ctrParams, ctrPath}
        md {ctxs, mdty: defaultMDType, ctrParams}
recTermBindPath _ _ = unsafeThrow "Either wasn't a TermBindPath or I forgot a case"

-- List Constructor
--    Data3 GADTMD TypeBind (List TypeBind) {-List Constructor-} Term Type
--    CtrListCons2 Constructor {-List Constructor-}

-- List CtrParam
--    Constructor2 CtrMD TermBind {-List CtrParam-}
--    CtrParamListCons2 CtrParam {-List CtrParam-}

-- List TypeArg
--    TNeu1 TNeuMD TypeVarID {-List TypeArg-}
--    TypeArgListCons2 (TypeArg) {-List TypeArg-}

-- List TypeBind
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    TypeBindListCons2 (TypeBind) {-List TypeBind-}