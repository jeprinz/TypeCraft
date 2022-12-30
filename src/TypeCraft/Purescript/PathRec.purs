module TypeCraft.Purescript.PathRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

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

type TermPathRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, termPath :: UpPath}
type TypePathRecValue = {ctxs :: AllContext, mdty :: MDType, typePath :: UpPath}
type CtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctrPath :: UpPath}
type CtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, ctrParamPath :: UpPath}
type TypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, typeArgPath :: UpPath}
type TypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, typeBindPath :: UpPath}
type TermBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, termBindPath :: UpPath}
type ListCtrPathRecValue = {ctxs :: AllContext, mdty :: MDType, listCtrPath :: UpPath}
type ListCtrParamPathRecValue = {ctxs :: AllContext, mdty :: MDType, listCtrParamPath :: UpPath}
type ListTypeArgPathRecValue = {ctxs :: AllContext, mdty :: MDType, listTypeArgPath :: UpPath}
type ListTypeBindPathRecValue = {ctxs :: AllContext, mdty :: MDType, listTypeBindPath :: UpPath}
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
recTermPath args {ctxs, ty, termPath: (Let2 md tBind@(TermBind xmd x) tyBinds defTy body bodyTy) : up} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let2 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, termPath: (Let4 md tBind@(TermBind _ x) tyBinds def defTy bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let4 {ctxs: ctxs', mdty: getMDType up, ty: ty, termPath: up} md
        {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs, mdty: defaultMDType, ty: defTy, term: def} --def
        {ctxs: ctxs', mdty: defaultMDType, ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, termPath: (App1 md {-Term-} t2 argTy outTy) : up} =
    if not (Arrow defaultArrowMD argTy outTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app1 {ctxs, mdty: getMDType up, ty: outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onRightOfApp= true}, ty: argTy, term: t2}
        argTy outTy
recTermPath args {ctxs, ty, termPath: (App2 md t1 {-Term-} argTy outTy) : up} =
    if not (argTy == ty) then unsafeThrow "dynamic type error detected" else
    args.app2 {ctxs, mdty: getMDType up, ty: outTy, termPath: up} md
        {ctxs, mdty: defaultMDType{onLeftOfApp= true}, ty: Arrow defaultArrowMD argTy outTy, term: t1}
        argTy outTy
recTermPath args {ctxs, ty, termPath: (Lambda3 md tbind@(TermBind _ x) argTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx= delete x ctxs.mdctx, ctx= delete x ctxs.ctx} in
    args.lambda3 {ctxs: ctxs', mdty: getMDType up, ty: Arrow defaultArrowMD argTy bodyTy, termPath: up}
        md tbind {ctxs: ctxs', mdty: defaultMDType, ty: argTy}
        bodyTy
recTermPath args {ctxs, ty, termPath: (Buffer1 md {-Term-} bufTy body bodyTy) : up} =
    if not (bufTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer1 {ctxs, mdty: getMDType up, ty: bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTermPath args {ctxs, ty, termPath: (Buffer3 md buf bufTy {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    args.buffer3 {ctxs, mdty: getMDType up, ty: bodyTy, termPath: up}
        md {ctxs, mdty: defaultMDType, ty: bufTy, term: buf}
        {ctxs, mdty: defaultMDType, ty: bufTy} bodyTy
recTermPath args {ctxs, ty, termPath: (TypeBoundary1 md c {-Term-}) : up} =
    args.typeBoundary1 {ctxs, mdty: getMDType up, ty: ty, termPath: up} md c
recTermPath args {ctxs, ty, termPath: (ContextBoundary1 md x c) : up} =
    args.contextBoundary1 {ctxs, mdty: getMDType up, ty: ty, termPath: up} md x c
recTermPath args {ctxs, ty, termPath: (TLet4 md tybind@(TypeBind _ x) tyBinds def {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs {mdkctx = delete x ctxs.mdkctx, kctx = delete x ctxs.kctx} in
    args.tLet4 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, termPath: up}
        md tybind {ctxs, mdty: defaultMDType, tyBinds} {ctxs: ctxs', mdty: defaultMDType, ty: def} bodyTy
recTermPath args {ctxs, ty, termPath: (Data4 md tyBind@(TypeBind _ x) tyBinds ctrs {-Term-} bodyTy) : up} =
    if not (bodyTy == ty) then unsafeThrow "dynamic type error detected" else
    let ctrIds = constructorIds ctrs in
    let ctxs' = ctxs {mdkctx = delete x ctxs.mdkctx, kctx = delete x ctxs.kctx
            ,ctx = filterKeys (\x -> not (member x ctrIds)) ctxs.ctx
            ,mdctx = filterKeys (\x -> not (member x ctrIds)) ctxs.mdctx} in
    args.data4 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, termPath: up}
        md tyBind {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ctrs} bodyTy
recTermPath _ _ = unsafeThrow "recTermPath given something that isn't a term path"







--  Type
--    Lambda2 LambdaMD TermBind {-Type-} Term Type
--    Let3 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
--    Buffer2 BufferMD Term {-Type-} Term Type
--    TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
--    CtrParam1 CtrParamMD {-Type-}
--    TypeArg1 TypeArgMD {-Type-}
--    Arrow1 ArrowMD {-Type-} Type
--    Arrow2 ArrowMD Type {-Type-}

--  Constructor
--    CtrListCons1 {-Constructor-} (List CtrParam)

-- CtrParam
--    CtrParamListCons1 {-CtrParam-} (List CtrParam)

-- TypeArg
--    TNeu1 TNeuMD TypeVarID {-List TypeArg-}
--    TypeArgListCons1 {-TypeArg-} (List TypeArg)

-- TypeBind
--    TLet1 TLetMD {-TypeBind-} (List TypeBind) Type Term Type
--    Data1 GADTMD {-TypeBind-} (List TypeBind) (List Constructor) Term Type
--    TypeBindListCons1 {-TypeBind-} (List TypeBind)

-- TermBind
--    Lambda1 LambdaMD {-TermBind-} Type Term Type
--    Let1 LetMD {-TermBind-} (List TypeBind) Term Type Term Type
--    Constructor1 CtrMD {-TermBind-} (List CtrParam)

-- List Constructor
--    Data3 GADTMD TypeBind (List TypeBind) {-List Constructor-} Term Type
--    CtrListCons2 Constructor {-List Constructor-}
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type

-- List CtrParam
--    Constructor2 CtrMD TermBind {-List CtrParam-}
--    CtrParamListCons2 CtrParam {-List CtrParam-}

-- List TypeArg
--    TypeArgListCons2 (TypeArg) {-List TypeArg-}

-- List TypeBind
--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    TypeBindListCons2 (TypeBind) {-List TypeBind-}