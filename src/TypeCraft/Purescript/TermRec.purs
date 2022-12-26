module TypeCraft.Purescript.TermRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.Substitution (Sub, combineSub, subChange, subChangeCtx, unify)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.TypeChangeAlgebra (isIdentity, invert)
import Data.Tuple (fst)
import TypeCraft.Purescript.TypeChangeAlgebra (getSubstitution)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Kinds (bindsToKind)

-- TODO: figure out how to use row polymorphism to remove redundancy in record definitions
type TermRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, mdty :: MDType, ty :: Type, term :: Term}
type TypeRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, ty :: Type}
type ListConstructorRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, ctrs :: List Constructor}
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
recTerm args {mdctx, mdkctx, kctx, ctx, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind xmd x) xty body bodyTy)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected" else
      if not (ty2 == bodyTy) then unsafeThrow "dynamic type error detected" else
        args.lambda md bind
            {mdctx, mdkctx, kctx: kctx, ctx, ty: xty}
            {mdkctx, mdctx : insert x xmd.varName mdctx, mdty: defaultMDType, kctx: kctx, ctx: (insert x ty1 ctx), ty: ty2, term : body}
            ty2
recTerm args {mdkctx, mdctx, kctx, ctx, ty: tyOut, term : (App md t1 t2 tyArg tyOut')}
    = if not (tyOut == tyOut') then unsafeThrow "dynamic type error: shouldn't happen" else
        args.app md {mdkctx, mdctx, mdty: defaultMDType{onLeftOfApp = true}, kctx, ctx, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {mdkctx, mdctx, mdty: defaultMDType{onRightOfApp = true}, kctx, ctx, ty: tyArg, term: t2}
        tyArg tyOut
recTerm args {mdkctx, mdctx, kctx, ctx, term : Var md x tyArgs} = args.var md x tyArgs
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Let md bind@(TermBind xmd x) tbinds def defTy body bodyTy}
    = if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
        let ctx' = insert x defTy ctx in -- TODO; should use number of tbinds here!
        let mdctx' = insert x xmd.varName mdctx in
        args.lett md bind tbinds {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: defTy, term: def}
            {mdkctx, mdctx, kctx, ctx, ty: defTy}
            {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: ty, term: body}
            bodyTy
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Data md tbind@(TypeBind xmd x) tbinds ctrs body bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    let kctx' = insert x (bindsToKind tbinds) kctx in
    let mdkctx' = insert x xmd.varName mdkctx in
    args.dataa md tbind tbinds {mdkctx: mdkctx', mdctx, kctx: kctx', ctx, ctrs}
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        -- TODO TODO TODO TODO: actually add constructors to the context!
        {mdkctx: mdkctx', mdctx, mdty: defaultMDType, kctx : kctx', ctx: union ctx (constructorTypes dataType ctrs), ty: ty, term: body}
        bodyTy
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : TLet md tybind@(TypeBind xmd x) tbinds def body bodyTy} =
    if not (bodyTy == ty) then unsafeThrow "shouldn't happen" else
    let kctx' = insert x (bindsToKind tbinds) kctx in
    let mdkctx' = insert x xmd.varName mdkctx in
    args.tlet md tybind tbinds
        {mdkctx, mdctx, kctx, ctx, ty: def}
        {mdkctx: mdkctx', mdctx, mdty: defaultMDType, kctx: kctx', ctx, ty: bodyTy, term: body}
        bodyTy
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen" else
    args.typeBoundary md c {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: snd (getEndpoints c), term: body}
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : ContextBoundary md x c body} =
    args.contextBoundary md x c {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx: insert x (snd (getEndpoints c)) ctx, ty: ty, term: body}
recTerm args {kctx, ctx, ty, term : Hole md} = args.hole md
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Buffer md def defTy body bodyTy} =
    args.buffer md
        {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: defTy, term: def}
        {mdkctx, mdctx, kctx, ctx, ty: defTy}
        {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: bodyTy, term: body}
        bodyTy
recTerm _ _ = unsafeThrow "invalid type for a lambda probably"