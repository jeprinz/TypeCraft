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

type TermPathRecValue = {kctx :: TypeContext, ctx :: TermContext, ty :: Type, termPath :: TermPath}
type TypePathRecValue = {kctx :: TypeContext, ctx :: TermContext, ty:: Type, typePath :: TypePath}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let2), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let1 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TypeRecValue -> TermRecValue -> Type -> a
    , let3 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TermRecValue -> TypeRecValue -> Type -> a
    , data3 :: TermPathRecValue -> GADTMD -> TypeBind -> List TypeBind -> List Constructor -> Type -> a
    , top :: a
}
type TypePathRec a = {
      arrow1 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
    , arrow2 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
    --Let2 TermPath LetMD TermBind (List TypeBind) Term {-Type-} Term Type
    , let2 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TermRecValue -> TermRecValue -> Type -> a
}

recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {kctx, ctx, ty, termPath: Let1 up md bind@(TermBind _ x) tBinds defTy body bodyTy} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    args.let1 {kctx, ctx: delete x ctx, ty: bodyTy, termPath: up} md bind tBinds
        {kctx, ctx, ty: defTy} -- defTy
        {kctx, ctx, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {kctx, ctx, ty, termPath: Let3 up md bind@(TermBind _ x) tBinds def defTy bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    args.let3 {kctx, ctx: delete x ctx, ty: ty, termPath: up} md bind tBinds
        {kctx, ctx, ty: defTy, term: def} --def
        {kctx, ctx, ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {kctx, ctx, ty, termPath: Data3 up md bind@(TypeBind _ x) tbinds ctrs bodyTy} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    args.data3 {kctx: delete x kctx, ctx, ty: ty, termPath: up} md bind tbinds ctrs bodyTy
recTermPath args {termPath: Top} = args.top
recTermPath _ _ = hole

recTypePath :: forall a. TypePathRec a -> TypePathRecValue -> a
recTypePath args {kctx, ctx, ty, typePath: Arrow1 up md outTy} =
    args.arrow1 {kctx, ctx, ty: Arrow defaultArrowMD ty outTy, typePath: up} md {kctx, ctx, ty: outTy}
recTypePath args {kctx, ctx, ty, typePath: Arrow2 up md inTy} =
    args.arrow2 {kctx, ctx, ty: Arrow defaultArrowMD inTy ty, typePath: up} md {kctx, ctx, ty: inTy}
recTypePath args {kctx, ctx, ty, typePath: Let2 up md bind@(TermBind _ x) tbinds def body bodyTy} =
    let ctx' = insert x ty ctx in
    args.let2 {kctx, ctx, ty: bodyTy, termPath: up} md bind tbinds
        {kctx, ctx: ctx', ty, term: def}
        {kctx, ctx: ctx', ty, term: body}
        bodyTy
recTypePath _ _ = hole