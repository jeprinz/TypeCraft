module TypeCraft.Purescript.ChangeType where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar (Change(..), ChangeParam(..), KindChange(..), Type(..), TypeParam(..), freshTypeHoleID)
import TypeCraft.Purescript.Context
import Data.Map.Internal (lookup)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.MD (defaultHoleMD, defaultTypeParamMD)
import Data.List (List(..), (:))

-- could avoid returning Type (because you can get it from the change with getEndpoints), if I put metadata into Change
chType :: KindChangeCtx -> Type -> Type /\ Change
chType kctx (Arrow md t1 t2) =
    let t1' /\ c1 = chType kctx t1 in
    let t2' /\ c2 = chType kctx t2 in
    Arrow md t1' t2' /\ CArrow c1 c2
chType kctx (THole md x) = THole md x /\ CHole x
chType kctx startType@(TNeu md x args) =
    case lookup x kctx of
    Nothing -> unsafeThrow "shouldn't get here! all variables should be bound in the context!"
    Just (TVarKindChange kindChange) ->
        let args' /\ cargs = chTypeParams kctx kindChange args in
        TNeu md x args' /\ CNeu x cargs
    Just TVarDelete ->
        let x = freshTypeHoleID unit in
        let newType = THole defaultHoleMD x in
        newType /\ Replace startType newType
    (Just (TVarTypeChange _)) -> unsafeThrow "I need to figure out what is the deal with TVarTypeChange!!!"


chTypeParams :: KindChangeCtx -> KindChange -> List TypeParam -> List TypeParam /\ List ChangeParam
chTypeParams kctx KCType Nil = Nil /\ Nil
chTypeParams kctx (KPlus kc) params =
    let tparams /\ cparams = chTypeParams kctx kc params in
    let x = freshTypeHoleID unit in
    let newType = THole defaultHoleMD x in
    (TypeParam defaultTypeParamMD newType : tparams) /\ (PlusParam newType : cparams)
chTypeParams kctx (KCArrow kc) (TypeParam md t : params) =
    let t' /\ c = chType kctx t in
    let tparams /\ cparams = chTypeParams kctx kc params in
    ((TypeParam md t') : tparams) /\ (ChangeParam c) : cparams
chTypeParams kctx (KMinus kc) (TypeParam md t : params) =
    let tparams /\ cparams = chTypeParams kctx kc params in
    tparams /\ (MinusParam t) : cparams
chTypeParams kctx _ _ = unsafeThrow "shouldn't get here: types didn't line up with kindchanges (or I missed a case)"
