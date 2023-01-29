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
import TypeCraft.Purescript.TypeChangeAlgebra (alterCtxVarChange)
import Debug (trace)

type TermRecValue = {ctxs :: AllContext, ty :: Type, term :: Term}
type TypeRecValue = {ctxs :: AllContext, ty :: Type}
type CtrRecValue = {ctxs :: AllContext, ctr :: Constructor}
type CtrParamRecValue = {ctxs :: AllContext, ctrParam :: CtrParam}
type TypeArgRecValue = {ctxs :: AllContext, tyArg :: TypeArg}
type TypeBindRecValue = {ctxs :: AllContext, tyBind :: TypeBind}
type TermBindRecValue = {ctxs :: AllContext, tBind :: TermBind}
type ListCtrRecValue = {ctxs :: AllContext, ctrs :: List Constructor}
type ListCtrParamRecValue = {ctxs :: AllContext, ctrParams :: List CtrParam}
type ListTypeArgRecValue = {ctxs :: AllContext, tyArgs :: List TypeArg}
type ListTypeBindRecValue = {ctxs :: AllContext, tyBinds :: List TypeBind}

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
    , contextBoundary :: ContextBoundaryMD -> TermVarID -> VarChange -> TermRecValue -> a
    , hole :: HoleMD -> a
    , buffer :: BufferMD -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
}

recTerm :: forall a. TermRec a -> TermRecValue -> a
recTerm args {ctxs, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind xmd x) xty body bodyTy)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected 8" else
      if not (ty2 == bodyTy) then unsafeThrow "dynamic type error detected 9" else
      let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x (PType ty1) ctxs.ctx} in
        args.lambda md {ctxs, tBind: bind}
            {ctxs, ty: xty}
            {ctxs: ctxs', ty: ty2, term : body}
            ty2
recTerm args {ctxs, ty: tyOut, term : (App md t1 t2 tyArg tyOut')}
    = if not (tyOut == tyOut') then unsafeThrow ("dynamic type error: shouldn't happen1. tyOut is: " <> show tyOut <> ", and tyOut' is: " <> show tyOut') else
        args.app md {ctxs, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {ctxs, ty: tyArg, term: t2}
        tyArg tyOut
recTerm args {ctxs, term : Var md x tyArgs} = args.var md x {ctxs, tyArgs}
recTerm args {ctxs, ty, term : Let md tBind@(TermBind xmd x) tyBinds def defTy body bodyTy}
    = if not (ty == bodyTy) then unsafeThrow "shouldn't happen recTerm let" else
        -- TODO; should use number of tbinds here!
        let ctxs' = addLetToCtx ctxs tBind tyBinds defTy in
        args.lett md {ctxs, tBind} {ctxs, tyBinds}
            {ctxs: ctxs',  ty: defTy, term: def}
            {ctxs, ty: defTy}
            {ctxs: ctxs', ty: ty, term: body}
            bodyTy
recTerm args {ctxs, ty, term : Data md tyBind@(TypeBind xmd x) tyBinds ctrs body bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "shouldn't happen recTerm data" else
    let ctxs' = addDataToCtx ctxs tyBind tyBinds ctrs in
    args.dataa md {ctxs, tyBind}
        {ctxs, tyBinds} {ctxs: ctxs', ctrs}
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        -- TODO TODO TODO TODO: actually add constructors to the context!
        {ctxs: ctxs', ty: ty, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TLet md tyBind@(TypeBind xmd x) tyBinds def body bodyTy} =
    if not (bodyTy == ty) then unsafeThrow "shouldn't happen recTerm TLet" else
    let ctxs' = addTLetToCtx ctxs tyBind tyBinds def in
    args.tlet md {ctxs, tyBind} {ctxs, tyBinds}
        {ctxs: ctxs', ty: def}
        {ctxs: ctxs', ty: bodyTy, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen recTerm typebound" else
    args.typeBoundary md c {ctxs, ty: fst (getEndpoints c), term: body}
recTerm args {ctxs, ty, term : ContextBoundary md x c body} =
    let ctxs' = ctxs{ctx = alterCtxVarChange ctxs.ctx x c} in
    args.contextBoundary md x c {ctxs, ty: ty, term: body}
recTerm args {term : Hole md} = args.hole md
recTerm args {ctxs, ty, term : Buffer md def defTy body bodyTy} =
    args.buffer md
        {ctxs, ty: defTy, term: def}
        {ctxs, ty: defTy}
        {ctxs, ty: bodyTy, term: body}
        bodyTy
recTerm _ term = unsafeThrow ("Missed all cases in recTerm. Term is: " <> show term.term <> " and type is: " <> show term.ty)

type TypeRec a = {
    arrow :: ArrowMD -> TypeRecValue -> TypeRecValue -> a
    , tHole :: THoleMD -> TypeHoleID -> a
    , tNeu :: TNeuMD -> TypeVarID -> ListTypeArgRecValue -> a
}

recType :: forall a. TypeRec a -> TypeRecValue -> a
recType args {ctxs, ty: Arrow md ty1 ty2} =
    args.arrow md {ctxs, ty: ty1}
        {ctxs, ty: ty2}
recType args {ctxs, ty: THole md id} = args.tHole md id
recType args {ctxs, ty: TNeu md x tyArgs} =
    args.tNeu md x {ctxs, tyArgs}

type CtrRec a = {
    ctr :: CtrMD -> TermBindRecValue -> ListCtrParamRecValue -> a
}

recCtr :: forall a. CtrRec a -> CtrRecValue -> a
recCtr args {ctxs, ctr: Constructor md tBind ctrParams}
    = args.ctr md {ctxs, tBind} {ctxs, ctrParams}

type CtrParamRec a = {
    ctrParam :: CtrParamMD -> TypeRecValue -> a
}

recCtrParam :: forall a. CtrParamRec a -> CtrParamRecValue -> a
recCtrParam args {ctxs, ctrParam: CtrParam md ty} =
    args.ctrParam md {ctxs, ty}

type TypeArgRec a = {
    typeArg :: TypeArgMD -> TypeRecValue -> a
}

recTypeArg :: forall a. TypeArgRec a -> TypeArgRecValue -> a
recTypeArg args {ctxs, tyArg: TypeArg md ty} =
    args.typeArg md {ctxs, ty}

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
    , nil :: Unit -> a
}

recListCtr :: forall a. ListCtrRec a -> ListCtrRecValue -> a
recListCtr args {ctxs, ctrs: ctr: ctrs} =
    args.cons {ctxs, ctr}
        {ctxs, ctrs}
recListCtr args thing@{ctxs, ctrs: Nil} = trace ("in recListCtr nil case, ctrs is: " <> show thing.ctrs) \_ -> args.nil unit

type ListCtrParamRec a = {
    cons :: CtrParamRecValue -> ListCtrParamRecValue -> a
    , nil :: Unit -> a
}

recListCtrParam :: forall a. ListCtrParamRec a -> ListCtrParamRecValue -> a
recListCtrParam args {ctxs, ctrParams: ctrParam: ctrParams} =
    args.cons {ctxs, ctrParam}
        {ctxs, ctrParams}
recListCtrParam args {ctxs, ctrParams: Nil} = args.nil unit

type ListTypeArgRec a = {
    cons :: TypeArgRecValue -> ListTypeArgRecValue -> a
    , nil :: Unit -> a
}

recListTypeArg :: forall a. ListTypeArgRec a -> ListTypeArgRecValue -> a
recListTypeArg args {ctxs, tyArgs: tyArg: tyArgs} =
    args.cons {ctxs, tyArg}
        {ctxs, tyArgs}
recListTypeArg args {ctxs, tyArgs: Nil} = args.nil unit

type ListTypeBindRec a = {
    cons :: TypeBindRecValue -> ListTypeBindRecValue -> a
    , nil :: a
}

recListTypeBind :: forall a. ListTypeBindRec a -> ListTypeBindRecValue -> a
recListTypeBind args {ctxs, tyBinds: tyBind: tyBinds} =
    args.cons {ctxs, tyBind}
        {ctxs, tyBinds}
recListTypeBind args {ctxs, tyBinds: Nil} = args.nil