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

type TermRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, term :: Term}
type TypeRecValue = {ctxs :: AllContext, ty :: Type}
type ListConstructorRecValue = {ctxs :: AllContext, ctrs :: List Constructor}

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
      lambda :: LambdaMD -> TermBind -> TypeRecValue -> TermRecValue -> Type -> a
    , app :: AppMD -> TermRecValue -> TermRecValue -> Type -> Type -> a
    , var :: VarMD -> TermVarID -> List TypeArg -> a
    , lett :: LetMD -> TermBind -> List TypeBind -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , dataa :: GADTMD -> TypeBind -> List TypeBind -> ListConstructorRecValue -> TermRecValue -> Type -> a -- TODO: write recConstructor!! Should be List ConstructorRecValue!
    , tlet :: TLetMD -> TypeBind -> List TypeBind -> TypeRecValue -> TermRecValue -> Type -> a
    , typeBoundary :: TypeBoundaryMD -> Change -> TermRecValue -> a
    , contextBoundary :: ContextBoundaryMD -> TermVarID -> Change -> TermRecValue -> a
    , hole :: HoleMD -> a
    , buffer :: BufferMD -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
}

recTerm :: forall a. TermRec a -> TermRecValue -> a
recTerm args {ctxs, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind xmd x) xty body bodyTy)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected" else
      if not (ty2 == bodyTy) then unsafeThrow "dynamic type error detected" else
      let ctxs' = ctxs{mdctx= insert x xmd.varName ctxs.mdctx, ctx= insert x ty1 ctxs.ctx} in
        args.lambda md bind
            {ctxs, ty: xty}
            {ctxs: ctxs', mdty: defaultMDType, ty: ty2, term : body}
            ty2
recTerm args {ctxs, ty: tyOut, term : (App md t1 t2 tyArg tyOut')}
    = if not (tyOut == tyOut') then unsafeThrow "dynamic type error: shouldn't happen" else
        args.app md {ctxs, mdty: defaultMDType{onLeftOfApp = true}, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {ctxs, mdty: defaultMDType{onRightOfApp = true}, ty: tyArg, term: t2}
        tyArg tyOut
recTerm args {ctxs, term : Var md x tyArgs} = args.var md x tyArgs
recTerm args {ctxs, ty, term : Let md bind@(TermBind xmd x) tbinds def defTy body bodyTy}
    = if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
        -- TODO; should use number of tbinds here!
        let ctxs' = ctxs{ctx = insert x defTy ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx} in
        args.lett md bind tbinds {ctxs: ctxs', mdty: defaultMDType, ty: defTy, term: def}
            {ctxs, ty: defTy}
            {ctxs: ctxs', mdty: defaultMDType, ty: ty, term: body}
            bodyTy
recTerm args {ctxs, ty, term : Data md tbind@(TypeBind xmd x) tbinds ctrs body bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    let ctxs' = ctxs{kctx = insert x (bindsToKind tbinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx
        , ctx= union ctxs.ctx (constructorTypes dataType ctrs)
        , mdctx= union ctxs.mdctx (constructorNames ctrs)} in
    args.dataa md tbind tbinds {ctxs: ctxs', ctrs}
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        -- TODO TODO TODO TODO: actually add constructors to the context!
        {ctxs: ctxs', mdty: defaultMDType, ty: ty, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TLet md tybind@(TypeBind xmd x) tbinds def body bodyTy} =
    if not (bodyTy == ty) then unsafeThrow "shouldn't happen" else
    let ctxs' = ctxs{kctx = insert x (bindsToKind tbinds) ctxs.kctx, mdkctx = insert x xmd.varName ctxs.mdkctx} in
    args.tlet md tybind tbinds
        {ctxs: ctxs', ty: def}
        {ctxs: ctxs', mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTerm args {ctxs, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen" else
    args.typeBoundary md c {ctxs, mdty: defaultMDType, ty: snd (getEndpoints c), term: body}
recTerm args {ctxs, ty, term : ContextBoundary md x c body} =
    let ctxs' = ctxs{ctx= insert x (snd (getEndpoints c)) ctxs.ctx} in
    args.contextBoundary md x c {ctxs, mdty: defaultMDType, ty: ty, term: body}
recTerm args {term : Hole md} = args.hole md
recTerm args {ctxs, ty, term : Buffer md def defTy body bodyTy} =
    args.buffer md
        {ctxs, mdty: defaultMDType, ty: defTy, term: def}
        {ctxs, ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
        bodyTy
recTerm _ _ = unsafeThrow "invalid type for a lambda probably"