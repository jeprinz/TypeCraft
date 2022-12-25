module TypeCraft.Purescript.PathRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, delete)
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
import TypeCraft.Purescript.TermRec (TermRecValue)
import TypeCraft.Purescript.TermRec (TypeRecValue)

type TermPathRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let3), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let1 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TypeRecValue -> TermRecValue -> Type -> a
    , let3 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TermRecValue -> TypeRecValue -> Type -> a
    , data3 :: TermPathRecValue -> GADTMD -> TypeBind -> List TypeBind -> List Constructor -> Type -> a
}

recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> Tooth -> a
recTermPath args {kctx, ctx, ty} (Let2 md bind@(TermBind _ x) tBinds defTy body bodyTy) =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    args.let1 {kctx, ctx: delete x ctx, ty: bodyTy} md bind tBinds
        {kctx, ctx, ty: defTy} -- defTy
        {kctx, ctx, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {kctx, ctx, ty} (Let4 md bind@(TermBind _ x) tBinds def defTy bodyTy) =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    args.let3 {kctx, ctx: delete x ctx, ty: ty} md bind tBinds
        {kctx, ctx, ty: defTy, term: def} --def
        {kctx, ctx, ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {kctx, ctx, ty} (Data3 md bind@(TypeBind _ x) tbinds ctrs bodyTy) =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    args.data3 {kctx: delete x kctx, ctx, ty: ty} md bind tbinds ctrs bodyTy
recTermPath _ _ _ = hole