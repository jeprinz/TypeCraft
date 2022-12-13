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
import TypeCraft.Purescript.ChangeType (chTypeParams)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)

type TermRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type, term :: Term}
type TypeRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type TermRec a = {
      lambda :: LambdaMD -> TermBind -> TypeRecValue -> TermRecValue -> a
    , app :: AppMD -> TermRecValue -> TermRecValue -> TypeRecValue -> a
    , var :: VarMD -> TermVarID -> List TypeParam -> a -- TODO: write recTypeParam!!!!! it should pass a List TypeParamValue or something!
    , lett :: LetMD -> TermBind -> (List TypeBind) -> TermRecValue -> TypeRecValue -> TermRecValue -> Type -> a
    , dataa :: GADTMD -> TypeBind -> List TypeBind -> List Constructor -> TermRecValue -> Type -> a -- TODO: write recConstructor!! Should be List ConstructorRecValue!
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
recTerm args {kctx, ctx, ty: tyOut, term : (App md t1 t2 tyArg)}
    = args.app md {kctx, ctx, ty: Arrow defaultArrowMD tyArg tyOut, term: t1}
        {kctx, ctx, ty: tyArg, term: t2}
        {kctx, ctx, ty: tyArg}
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
        {kctx : insert x (Type defaultTypeMD) kctx, ctx: union ctx (constructorTypes dataType ctrs), ty: ty, term: body}
        bodyTy
recTerm _ _ = hole
--          | Let LetMD TermBind (List TypeBind) Term Type Term
--          | Data GADTMD TypeBind (List TypeBind) (List Constructor) Term
--          | TLet TLetMD TypeBind (List TypeBind) Type Kind Term
--          | TypeBoundary TypeBoundaryMD Change Term -- the change goes from type inside to type outside. That is, getEndpoints gives inside type on left and outside on right.
--          | ContextBoundary ContextBoundaryMD TermVarID Change Term
--          | Hole HoleMD
--          | Buffer BufferMD Term Type Term

recType :: forall a. TypeRec a -> TypeRecValue -> a
recType args {kctx, ctx, ty: Arrow md t1 t2} =
    args.arrow md {kctx, ctx, ty: t1} {kctx, ctx, ty: t2}
recType _ _ = hole
