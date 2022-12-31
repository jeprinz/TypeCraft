module TypeCraft.Purescript.ShallowEmbed where
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Context
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.List (List(..), (:))

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Util (hole)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.MD (defaultVarMD)
import TypeCraft.Purescript.MD (defaultLambdaMD)

{-
This file defines a shallow embedding to make it easier to write terms for testing purposes
-}

type CtxAndType = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type STerm = CtxAndType -> Term

lambda :: String -> (Term -> STerm) -> STerm
lambda name body {kctx, ctx, ty: Arrow _ ty1 ty2} =
    let x = freshInt unit in
    let t = body (Var defaultVarMD x Nil) {kctx, ctx: insert x (PType ty1) ctx, ty: ty1} in
    Lambda defaultLambdaMD (TermBind {varName: name} x) ty1 t ty2
lambda _ _ _ = unsafeThrow "shouldn't happen"

program :: STerm -> Type -> Term
program t ty = t {kctx: empty, ctx: empty, ty: ty}
