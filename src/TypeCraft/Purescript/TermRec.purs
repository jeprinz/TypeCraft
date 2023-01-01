module TypeCraft.Purescript.TermRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import Data.Tuple (fst)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.TypeChangeAlgebra (pGetEndpoints)

type TermRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, term :: Term}
type TypeRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type}
type CtrRecValue = {ctxs :: AllContext, mdty :: MDType, ctr :: Constructor}
type CtrParamRecValue = {ctxs :: AllContext, mdty :: MDType, ctrParam :: CtrParam}
type TypeArgRecValue = {ctxs :: AllContext, mdty :: MDType, tyArg :: TypeArg}
type TypeBindRecValue = {ctxs :: AllContext, mdty :: MDType, tyBind :: TypeBind}
type TermBindRecValue = {ctxs :: AllContext, mdty :: MDType, tBind :: TermBind}
type ListCtrRecValue = {ctxs :: AllContext, mdty :: MDType, ctrs :: List Constructor}
type ListCtrParamRecValue = {ctxs :: AllContext, mdty :: MDType, ctrParams :: List CtrParam}
type ListTypeArgRecValue = {ctxs :: AllContext, mdty :: MDType, tyArgs :: List TypeArg}
type ListTypeBindRecValue = {ctxs :: AllContext, mdty :: MDType, tyBinds :: List TypeBind}

-- TODO: make a RecValue for each grammatical sort. Even if I don't write recursors for all of them, at least those might be useful!

{-
There isn't really any needs for recursors on grammatical sorts other than terms, because no other part of the syntax
binds anything into the context or does anything nontrivial with types.

Likewise, it is only necessary to have RecValues for parts of the syntax where something interesting happens with the context.
-}

-- TODO: possible refactoring to make TermToNode simpler:
-- replace *RecValue with *CursorLocation
-- I also need to get selections out though?
-- So pathRec will need to have a path to the bottom!?

type TermRec a = {
      lambda :: LambdaMD -> TermBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , app :: AppMD -> TermRecValue -> TermRecValue -> Type -> Type -> a
    , var :: VarMD -> TermVarID -> ListTypeArgRecValue -> a
    , lett :: LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , dataa :: GADTMD -> TypeBindRecValue -> ListTypeBindRecValue -> ListCtrRecValue -> TermRecValue -> Type -> a -- TODO: write recConstructor!! Should be List ConstructorRecValue!
    , tlet :: TLetMD -> TypeBindRecValue -> ListTypeBindRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , typeBoundary :: TypeBoundaryMD -> Change -> TermRecValue -> a
    , contextBoundary :: ContextBoundaryMD -> TermVarID -> PolyChange -> TermRecValue -> a
    , hole :: HoleMD -> a
    , buffer :: BufferMD -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
}

recTerm :: forall a. TermRec a -> TermRecValue -> a
recTerm args {ctxs, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind xmd x) xty body bodyTy)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected" else
      if not (ty2 == bodyTy) then unsafeThrow "dynamic type error detected" else
      let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType ty1) ctxs.ctx} in
        args.lambda md {ctxs, mdty: defaultMDType, tBind: bind}
            {ctxs, mdty: defaultMDType, ty: xty}
            {ctxs: ctxs', mdty: defaultMDType, ty: ty2, term : body}
            ty2
recTerm args {ctxs, ty: tyOut, term : (App md t1 t2 tyArg tyOut')}
    = if not (tyOut == tyOut') then unsafeThrow "dynamic type error: shouldn't happen" else
        args.app md {ctxs, mdty: defaultMDType{onLeftOfApp = true}, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {ctxs, mdty: defaultMDType{onRightOfApp = true}, ty: tyArg, term: t2}
        tyArg tyOut
recTerm args {ctxs, term : Var md x tyArgs} = args.var md x {ctxs, mdty: defaultMDType, tyArgs}
recTerm args {ctxs, ty, term : Let md tBind@(TermBind xmd x) tyBinds def defTy body bodyTy}
    = if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
        -- TODO; should use number of tbinds here!
        let ctxs' = ctxs{ctx = insert x (tyBindsWrapType tyBinds defTy) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
        args.lett md {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, tyBinds}
            {ctxs: ctxs', mdty: defaultMDType, ty: defTy, term: def}
            {ctxs, mdty: defaultMDType, ty: defTy}
            {ctxs: ctxs', mdty: defaultMDType, ty: ty, term: body}
            bodyTy
recTerm args {ctxs, ty, term : Data md tyBind@(TypeBind xmd x) tyBinds ctrs body bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.dataa md {ctxs, mdty: defaultMDType, tyBind}
        {ctxs, mdty: defaultMDType, tyBinds} {ctxs: ctxs', mdty: defaultMDType, ctrs}
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        -- TODO TODO TODO TODO: actually add constructors to the context!
        {ctxs: ctxs', mdty: defaultMDType, ty: ty, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TLet md tyBind@(TypeBind xmd x) tyBinds def body bodyTy} =
    if not (bodyTy == ty) then unsafeThrow "shouldn't happen" else
    let ctxs' = ctxs{kctx = insert x (bindsToKind tyBinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx} in
    args.tlet md {ctxs, mdty: defaultMDType, tyBind} {ctxs, mdty: defaultMDType, tyBinds}
        {ctxs: ctxs', mdty: defaultMDType, ty: def}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen" else
    args.typeBoundary md c {ctxs, mdty: defaultMDType, ty: snd (getEndpoints c), term: body}
recTerm args {ctxs, ty, term : ContextBoundary md x c body} =
    let ctxs' = ctxs{ctx= insert x (snd (pGetEndpoints c)) ctxs.ctx} in
    args.contextBoundary md x c {ctxs, mdty: defaultMDType, ty: ty, term: body}
recTerm args {term : Hole md} = args.hole md
recTerm args {ctxs, ty, term : Buffer md def defTy body bodyTy} =
    args.buffer md
        {ctxs, mdty: defaultMDType, ty: defTy, term: def}
        {ctxs, mdty: defaultMDType, ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTerm _ _ = unsafeThrow "invalid type for a lambda probably"

type TypeRec a = {
    arrow :: ArrowMD -> TypeRecValue -> TypeRecValue -> a
    , tHole :: THoleMD -> TypeHoleID -> a
    , tNeu :: TNeuMD -> TypeVarID -> ListTypeArgRecValue -> a
}

recType :: forall a. TypeRec a -> TermRecValue -> a
recType args {ctxs, ty: Arrow md ty1 ty2} =
    args.arrow md {ctxs, mdty: defaultMDType{onLeftOfArrow= true}, ty: ty1}
        {ctxs, mdty: defaultMDType, ty: ty2}
recType args {ctxs, ty: THole md id} = args.tHole md id
recType args {ctxs, ty: TNeu md x tyArgs} =
    args.tNeu md x {ctxs, mdty: defaultMDType, tyArgs}

type CtrRec a = {
    ctr :: CtrMD -> TermBindRecValue -> ListCtrParamRecValue -> a
}

recCtr :: forall a. CtrRec a -> CtrRecValue -> a
recCtr args {ctxs, ctr: Constructor md tBind ctrParams}
    = args.ctr md {ctxs, mdty: defaultMDType, tBind} {ctxs, mdty: defaultMDType, ctrParams}

type CtrParamRec a = {
    ctrParam :: CtrParamMD -> TypeRecValue -> a
}

recCtrParam :: forall a. CtrParamRec a -> CtrParamRecValue -> a
recCtrParam args {ctxs, ctrParam: CtrParam md ty} =
    args.ctrParam md {ctxs, mdty: defaultMDType, ty}

type TypeArgRec a = {
    typeArg :: TypeArgMD -> TypeRecValue -> a
}

recTypeArg :: forall a. TypeArgRec a -> TypeArgRecValue -> a
recTypeArg args {ctxs, tyArg: TypeArg md ty} =
    args.typeArg md {ctxs, mdty: defaultMDType, ty}

type TermBindRec a = {
    termBind :: TermBindMD -> TermVarID -> a
}

recTermBind :: forall a. TermBindRec a -> TermBindRecValue -> a
recTermBind args {ctxs, tBind: TermBind md x} = args.termBind md x

type TypeBindRec a = {
    typeBind :: TypeBindMD -> TypeVarID -> a
}

recTypeBind :: forall a. TypeBindRec a -> TypeBindRecValue -> a
recTypeBind args {ctxs, tyBind: TypeBind md x} = args.typeBind md x

type ListCtrRec a = {
    cons :: CtrRecValue -> ListCtrRecValue -> a
    , nil :: a
}

recListCtr :: forall a. ListCtrRec a -> ListCtrRecValue -> a
recListCtr args {ctxs, ctrs: ctr: ctrs} =
    args.cons {ctxs, mdty:defaultMDType, ctr}
        {ctxs, mdty:defaultMDType, ctrs}
recListCtr args {ctxs, ctrs: Nil} = args.nil

type ListCtrParamRec a = {
    cons :: CtrParamRecValue -> ListCtrParamRecValue -> a
    , nil :: a
}

recListCtrParam :: forall a. ListCtrParamRec a -> ListCtrParamRecValue -> a
recListCtrParam args {ctxs, ctrParams: ctrParam: ctrParams} =
    args.cons {ctxs, mdty:defaultMDType, ctrParam}
        {ctxs, mdty:defaultMDType, ctrParams}
recListCtrParam args {ctxs, ctrParams: Nil} = args.nil

type ListTypeArgRec a = {
    cons :: TypeArgRecValue -> ListTypeArgRecValue -> a
    , nil :: a
}

recTypeArgParam :: forall a. ListTypeArgRec a -> ListTypeArgRecValue -> a
recTypeArgParam args {ctxs, tyArgs: tyArg: tyArgs} =
    args.cons {ctxs, mdty:defaultMDType, tyArg}
        {ctxs, mdty:defaultMDType, tyArgs}
recTypeArgParam args {ctxs, tyArgs: Nil} = args.nil

type ListTypeBindRec a = {
    cons :: TypeBindRecValue -> ListTypeBindRecValue -> a
    , nil :: a
}

recTypeBindParam :: forall a. ListTypeBindRec a -> ListTypeBindRecValue -> a
recTypeBindParam args {ctxs, tyBinds: tyBind: tyBinds} =
    args.cons {ctxs, mdty:defaultMDType, tyBind}
        {ctxs, mdty:defaultMDType, tyBinds}
recTypeBindParam args {ctxs, tyBinds: Nil} = args.nil