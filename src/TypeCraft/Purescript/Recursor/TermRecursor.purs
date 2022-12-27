module TypeCraft.Purescript.Recursor.TermRecursor where

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
import TypeCraft.Purescript.MD

type TermRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, mdty :: MDType, ty :: Type, term :: Term}
type TypeRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type TypeRec' ty = (
      arrow :: ArrowMD -> ty -> ty -> ty
    , tHole :: THoleMD -> TypeHoleID -> ty
    , tNeu :: TNeuMD -> TypeVarID -> (List (TypeArgMD /\ ty)) -> ty
)

type TypeRec ty = {|TypeRec' ty}

type TermRec term ty = {
      lambda :: LambdaMD -> TermBind -> ty -> term -> term
    , app :: AppMD -> term -> term -> Type -> term
    , var :: VarMD -> TermVarID -> List TypeArg -> term
    , lett :: LetMD -> TermBind -> List TypeBind -> term -> ty -> term -> term
    , dataa :: GADTMD -> TypeBind -> List TypeBind -> List Constructor -> term -> term
    , tlet :: TLetMD -> TypeBind -> List TypeBind -> ty -> term -> term
    , typeBoundary :: TypeBoundaryMD -> Change -> term -> term
    , contextBoundary :: ContextBoundaryMD -> TermVarID -> Change -> term -> term
    , hole :: HoleMD -> term
    , buffer :: BufferMD -> term -> ty -> term -> term
    | TypeRec' ty
}

recTerm :: forall term ty. TermRec term ty -> TermRecValue -> term
recTerm args {mdctx, mdkctx, kctx, ctx, ty: (Arrow _ ty1 ty2), term : (Lambda md bind@(TermBind xmd x) xty body)}
    = if not (ty1 == xty) then unsafeThrow "dynamic type error detected" else
        args.lambda md bind
            (recType args {mdctx, mdkctx, kctx: kctx, ctx, ty: xty})
            (recTerm args {mdkctx, mdctx : insert x xmd.varName mdctx, mdty: defaultMDType, kctx: kctx, ctx: (insert x ty1 ctx), ty: ty2, term : body})
recTerm args {mdkctx, mdctx, kctx, ctx, ty: tyOut, term : (App md t1 t2 tyArg)} =
        args.app md (recTerm args {mdkctx, mdctx, mdty: defaultMDType{onLeftOfApp = true}, kctx, ctx, ty: Arrow defaultArrowMD tyArg tyOut, term: t1})
        (recTerm args {mdkctx, mdctx, mdty: defaultMDType{onRightOfApp = true}, kctx, ctx, ty: tyArg, term: t2})
        tyArg
recTerm args {mdkctx, mdctx, kctx, ctx, term : Var md x tyArgs} = args.var md x tyArgs
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Let md bind@(TermBind xmd x) tbinds def defTy body} =
        let ctx' = insert x defTy ctx in -- TODO; should use number of tbinds here!
        let mdctx' = insert x xmd.varName mdctx in
        args.lett md bind tbinds (recTerm args {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: defTy, term: def})
            (recType args {mdkctx, mdctx, kctx, ctx, ty: defTy})
            (recTerm args {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: ty, term: body})
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Data md tbind@(TypeBind xmd x) tbinds ctrs body} =
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    let kctx' = insert x (bindsToKind tbinds) kctx in
    let mdkctx' = insert x xmd.varName mdkctx in
    args.dataa md tbind tbinds ctrs -- {mdkctx: mdkctx', mdctx, kctx: kctx', ctx, ctrs}
        -- TODO: on line below, don't just put Type for kind, actually use the list of tbinds to get the number of parameters!!!!
        -- TODO TODO TODO TODO: actually add constructors to the context!
        (recTerm args {mdkctx: mdkctx', mdctx, mdty: defaultMDType, kctx : kctx', ctx: union ctx (constructorTypes dataType ctrs), ty: ty, term: body})
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : TLet md tybind@(TypeBind xmd x) tbinds def body} =
    let kctx' = insert x (bindsToKind tbinds) kctx in
    let mdkctx' = insert x xmd.varName mdkctx in
    args.tlet md tybind tbinds
        (recType args {mdkctx, mdctx, kctx, ctx, ty: def})
        (recTerm args {mdkctx: mdkctx', mdctx, mdty: defaultMDType, kctx: kctx', ctx, ty: ty, term: body})
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : TypeBoundary md c body} =
    if not (ty == snd (getEndpoints c)) then unsafeThrow "shouldn't happen" else
    args.typeBoundary md c (recTerm args {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: snd (getEndpoints c), term: body})
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : ContextBoundary md x c body} =
    args.contextBoundary md x c (recTerm args {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx: insert x (snd (getEndpoints c)) ctx, ty: ty, term: body})
recTerm args {kctx, ctx, ty, term : Hole md} = args.hole md
recTerm args {mdkctx, mdctx, kctx, ctx, ty, term : Buffer md def defTy body} =
    args.buffer md
        (recTerm args {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: defTy, term: def})
        (recType args {mdkctx, mdctx, kctx, ctx, ty: defTy})
        (recTerm args {mdkctx, mdctx, mdty: defaultMDType, kctx, ctx, ty: ty, term: body})
recTerm _ _ = unsafeThrow "invalid type for a lambda probably"

recType :: forall term ty. TermRec term ty -> TypeRecValue -> ty
recType = hole
