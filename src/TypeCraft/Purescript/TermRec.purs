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

type TermRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type, term :: Term}
type TypeRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type TermRec a = {
      lambda :: LambdaMD -> TermBind -> TypeRecValue -> TermRecValue -> a
    , app :: AppMD -> TermRecValue -> TermRecValue -> Type -> Type -> a
    , var :: VarMD -> TermVarID -> List TypeArg -> a -- TODO: write recTypeParam!!!!! it should pass a List TypeParamValue or something!
    , lett :: LetMD -> TermBind -> (List TypeBind) -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , dataa :: GADTMD -> TypeBind -> List TypeBind -> List Constructor -> TermRecValue -> Type -> a -- TODO: write recConstructor!! Should be List ConstructorRecValue!
    , tlet :: TLetMD -> TypeBind -> List TypeBind -> TypeRecValue -> TermRecValue -> Type -> a
    , typeBoundary :: TypeBoundaryMD -> Change -> TermRecValue -> a
    , contextBoundary :: ContextBoundaryMD -> TermVarID -> Change -> TermRecValue -> a
    , hole :: HoleMD -> a
    , buffer :: BufferMD -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
}

type TypeRec a = {
    arrow :: ArrowMD -> TypeRecValue -> TypeRecValue -> a
}

recTerm :: forall a. TermRec a -> TermRecValue -> a
recTerm args {kctx, ctx, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind _ x) xty body)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected" else
        args.lambda md bind
            {kctx: kctx, ctx, ty: xty}
            {kctx: kctx, ctx: (insert x ty1 ctx), ty: ty2, term : body}
recTerm args {kctx, ctx, ty: tyOut, term : (App md t1 t2 tyArg tyOut')}
    = if not (tyOut == tyOut') then unsafeThrow "dynamic type error: shouldn't happen" else
        args.app md {kctx, ctx, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {kctx, ctx, ty: tyArg, term: t2}
        tyArg tyOut
recTerm args {ctx, term : Var md x tyParams} = args.var md x tyParams
recTerm args {kctx, ctx, ty, term : Let md bind@(TermBind _ x) tbinds def defTy body bodyTy}
    = if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
        let ctx' = insert x defTy ctx in -- TODO; should use number of tbinds here!
        args.lett md bind tbinds {kctx, ctx: ctx', ty: defTy, term: def}
            {kctx, ctx, ty: defTy}
            {kctx, ctx: ctx', ty: ty, term: body}
            bodyTy
recTerm args {kctx, ctx, ty, term : Data md tbind@(TypeBind _ x) tbinds ctrs body bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "shouldn't happen" else
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    args.dataa md tbind tbinds ctrs
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        {kctx : insert x (bindsToKind tbinds) kctx, ctx: union ctx (constructorTypes dataType ctrs), ty: ty, term: body}
        bodyTy
recTerm args {kctx, ctx, ty, term : TLet md tybind@(TypeBind _ x) tbinds def body bodyTy} =
    if not (bodyTy == ty) then unsafeThrow "shouldn't happen" else
    let kctx' = insert x (bindsToKind tbinds) kctx in
    args.tlet md tybind tbinds
        {kctx, ctx, ty: def}
        {kctx: kctx', ctx, ty: bodyTy, term: body}
        bodyTy
recTerm args {kctx, ctx, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen" else
    args.typeBoundary md c {kctx, ctx, ty: snd (getEndpoints c), term: body}
recTerm args {kctx, ctx, ty, term : ContextBoundary md x c body} =
    args.contextBoundary md x c {kctx, ctx: insert x (snd (getEndpoints c)) ctx, ty: ty, term: body}
recTerm args {kctx, ctx, ty, term : Hole md} = args.hole md
recTerm args {kctx, ctx, ty, term : Buffer md def defTy body bodyTy} =
    args.buffer md
        {kctx, ctx, ty: defTy, term: def}
        {kctx, ctx, ty: defTy}
        {kctx, ctx, ty: bodyTy, term: body}
        bodyTy
recTerm _ _ = unsafeThrow "invalid type for a lambda probably"

recType :: forall a. TypeRec a -> TypeRecValue -> a
recType args {kctx, ctx, ty: Arrow md t1 t2} =
    args.arrow md {kctx, ctx, ty: t1} {kctx, ctx, ty: t2}
-- THole
-- TNeu
recType _ _ = hole
