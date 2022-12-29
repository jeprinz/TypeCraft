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
import Data.Tuple (fst)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermRec

type TermPathRecValue = {ctxs :: AllContext, mdty :: MDType, ty :: Type, termPath :: UpPath}
-- TypePathRecValue needs ctx and ty so that when it gets up to a TermPath (e.g. in Let3), it knows the context and type

-- TODO: in the future, when I implement editing lists of constructors and stuff, more things will need to be
-- <thing>RecValue instead of just <thing>
type TermPathRec a = {
      let2 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TypeRecValue -> TermRecValue -> Type -> a
    , let4 :: TermPathRecValue -> LetMD -> TermBind -> List TypeBind -> TermRecValue -> TypeRecValue -> Type -> a
    , data4 :: TermPathRecValue -> GADTMD -> TypeBind -> List TypeBind -> List Constructor -> Type -> a
}

getMDType :: UpPath -> MDType
getMDType (App1 _ _ _ _ : _ : _) = defaultMDType{onLeftOfApp = true}
getMDType (App2 _ _ _ _ : _ : _) = defaultMDType{onRightOfApp = true}
getMDType _ = defaultMDType

getParentMDType :: UpPath -> MDType
getParentMDType (_ : teeth) = getMDType teeth
getParentMDType _ = defaultMDType

recTermPath :: forall a. TermPathRec a -> TermPathRecValue -> a
recTermPath args {ctxs, ty, termPath: (Let2 md bind@(TermBind xmd x) tBinds defTy body bodyTy) : up} =
    if not (ty == defTy) then unsafeThrow "dynamic type error detected" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let2 {ctxs: ctxs', mdty: getMDType up, ty: bodyTy, termPath: up} md bind tBinds
        {ctxs: ctxs', ty: defTy}
        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body} -- body
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, termPath: (Let4 md bind@(TermBind _ x) tBinds def defTy bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdctx = delete x ctxs.mdctx, ctx = delete x ctxs.ctx} in
    args.let4 {ctxs: ctxs', mdty: getMDType up, ty: ty, termPath: up} md bind tBinds
        {ctxs, mdty: defaultMDType, ty: defTy, term: def} --def
        {ctxs: ctxs', ty: defTy} -- defTy
        bodyTy -- bodyTy
recTermPath args {ctxs, ty, termPath: (Data4 md bind@(TypeBind _ x) tbinds ctrs bodyTy) : up} =
    if not (ty == bodyTy) then unsafeThrow "dynamic type error detedted" else
    let ctxs' = ctxs{mdkctx = delete x ctxs.mdkctx,kctx = delete x ctxs.kctx} in
    args.data4 {ctxs: ctxs', mdty: getMDType up, ty: ty, termPath: up} md bind tbinds ctrs bodyTy
recTermPath _ _ = hole