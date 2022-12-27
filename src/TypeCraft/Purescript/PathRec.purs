module TypeCraft.Purescript.PathRec where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert, delete, union)
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
import TypeCraft.Purescript.Kinds (bindsToKind)

type TermPathRecValue = {mdkctx :: MDTypeContext, mdctx :: MDTermContext, mdty :: MDType, kctx :: TypeContext, ctx :: TermContext, ty :: Type, termPath :: DownPath}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let3), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let2 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind {-def-} -> TypeRecValue -> TermRecValue ->  a
    , let4 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TermRecValue -> TypeRecValue {-body-} -> a
    , data3 :: TermPathRecValue -> GADTMD -> TypeBind -> List TypeBind -> List Constructor {-body-} -> a
}

-- recurses DOWNWARDS!
recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {mdkctx, mdctx, kctx, ctx, ty, termPath : (Let2 md bind@(TermBind xmd x) tBinds defTy body) : down} =
    let mdctx' = insert x xmd.varName mdctx in
    let ctx' = insert x defTy ctx in
    args.let2 {mdkctx, mdctx: mdctx', mdty: hole, kctx, ctx: ctx', ty: defTy, termPath: down} md bind tBinds
        {mdkctx, mdctx, kctx, ctx, ty: defTy} -- defTy
        {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: ty, term: body} -- body
recTermPath args {mdkctx, mdctx, kctx, ctx, ty, termPath: (Let4 md bind@(TermBind xmd x) tBinds def defTy : down)} =
    let mdctx' = insert x xmd.varName mdctx in
    let ctx' = insert x defTy ctx in
    args.let4 {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx: ctx', ty: ty, termPath: down} md bind tBinds
        {mdkctx, mdctx: mdctx', mdty: defaultMDType, kctx, ctx, ty: defTy, term: def} --def
        {mdkctx, mdctx, kctx, ctx, ty: defTy} -- defTy
recTermPath args {mdkctx, mdctx, kctx, ctx, ty, termPath: (Data3 md tbind@(TypeBind xmd x) tbinds ctrs) : down} =
-- TODO: when I fix up the DATA case from termRec, I should copy over changes to here!
--    args.data3 {kctx: delete x kctx, ctx, ty: ty} md bind tbinds ctrs bodyTy
    let dataType = TNeu defaultTNeuMD x Nil in -- TODO: should actually use tbinds to get the list! ?? (sort of, the parametrs should be outside? see how constructorTypes changes)
    let kctx' = insert x (bindsToKind tbinds) kctx in
    let mdkctx' = insert x xmd.varName mdkctx in
    args.data3
        {mdkctx: mdkctx', mdctx, mdty: defaultMDType, kctx : kctx', ctx: union ctx (constructorTypes dataType ctrs), ty: ty, termPath: down}
        md tbind tbinds ctrs
recTermPath _ _ = hole