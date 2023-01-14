module TypeCraft.Purescript.ShallowEmbed where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD

import Data.List (List(..), (:))
import Data.List as List
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.UUID (genUUID)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Unsafe (unsafePerformEffect)
import TypeCraft.Purescript.Util (hole)

{-
This file defines a shallow embedding to make it easier to write terms for testing purposes
-}

type CtxAndType = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type STerm = CtxAndType -> Term
type SType = {kctx :: TypeContext, ctx :: TermContext} -> Type

slambda :: String -> (TermVarID -> STerm) -> STerm
slambda name body {kctx, ctx, ty: Arrow _ ty1 ty2} =
    let x = unsafePerformEffect genUUID in
    let t = body x {kctx, ctx: insert x (PType ty1) ctx, ty: ty2} in
    Lambda defaultLambdaMD (TermBind {varName: name} x) ty1 t ty2
slambda _ _ _ = unsafeThrow "shouldn't happen slambda"

slet :: String -> Array TypeBind -> (TermVarID -> STerm) -> SType -> (TermVarID -> STerm) -> STerm
slet name tyPrms def defTy body {kctx, ctx, ty} =
    let x = unsafePerformEffect genUUID in
    let defTy' = (defTy {kctx, ctx}) in
    let ctx' = insert x (List.foldr (\(TypeBind _ y) -> Forall y) (PType defTy') tyPrms) ctx in
    let def' = def x {kctx, ctx: ctx', ty: defTy'} in
    let body' = body x {kctx, ctx: ctx', ty: ty} in
    Let defaultLetMD (TermBind {varName: name} x) (List.fromFoldable tyPrms) def' defTy' body' ty

slet' :: String -> (TermVarID -> STerm) -> SType -> (TermVarID -> STerm) -> STerm
slet' name def defTy body {kctx, ctx, ty} =
    let x = unsafePerformEffect genUUID in
    let defTy' = (defTy {kctx, ctx}) in
    let ctx' = insert x (PType defTy') ctx in
    let def' = def x {kctx, ctx: ctx', ty: defTy'} in
    let body' = body x {kctx, ctx: ctx', ty: ty} in
    Let defaultLetMD (TermBind {varName: name} x) Nil def' defTy' body' ty

sapp :: STerm -> SType -> STerm -> STerm
sapp t1 argTy t2 {kctx, ctx, ty} = let argTy' = argTy {kctx, ctx} in
    App defaultAppMD (t1 {kctx, ctx, ty: Arrow defaultArrowMD argTy' ty}) (t2 {kctx, ctx, ty: argTy'}) argTy' ty

sTHole :: STerm
sTHole _ = Hole defaultHoleMD

sBindHole :: forall a. (TypeHoleID -> a) -> a
sBindHole bla = bla (freshTypeHoleID unit)

shole :: TypeHoleID -> SType
shole x _ = THole defaultTHoleMD x

sarrow :: SType -> SType -> SType
sarrow ty1 ty2 ct = Arrow defaultArrowMD (ty1 ct) (ty2 ct)

svar :: TermVarID -> STerm
svar x _ = Var defaultVarMD x Nil

program :: SType -> STerm -> Type /\ Term
program ty t = let ty' = (ty {kctx: empty, ctx: empty}) in ty' /\ (t {kctx: empty, ctx: empty, ty: ty'})

--tyProgram :: SType -> Type
--tyProgram ty = ty {kctx: empty, ctx: empty}

exampleType1 :: Type
exampleType1 = THole defaultHoleMD (unsafePerformEffect genUUID)

--exampleTerm1 :: Term
--exampleTerm1 = program (
--    slambda "x" (\x -> svar x)
--    ) exampleType1

exampleProg2 :: Type /\ Term
exampleProg2 =
    sBindHole \hole1 -> sBindHole \hole2 -> sBindHole \hole3 ->
        program (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
            (slambda "x" \x -> (slambda "y" \y -> sTHole))

exampleProg3 :: Type /\ Term
exampleProg3 =
    sBindHole \hole1 -> sBindHole \hole2 -> sBindHole \hole3 ->
        program (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
            (slambda "x" \x -> (slambda "y" \y -> svar x))

exampleProg4 :: Type /\ Term
exampleProg4 =
    sBindHole \hole1 -> sBindHole \hole2 -> sBindHole \hole3 ->
        program (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
            (slet' "f" (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
                (\f -> svar f))

exampleProg5 :: Type /\ Term
exampleProg5 =
    sBindHole \hole1 -> sBindHole \hole2 -> sBindHole \hole3 ->
        program (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
            (slet' "f" (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
                (\f -> (sapp (sapp (svar f) (shole hole1) sTHole) (shole hole2) sTHole)))

exampleProg6 :: Type /\ Term
exampleProg6 =
    sBindHole \hole1 -> sBindHole \hole2 -> sBindHole \hole3 ->
        program (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
            (slet "f" [ TypeBind {varName: "A"} (unsafePerformEffect genUUID) ] (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (shole hole1) (sarrow (shole hole2) (shole hole3)))
                (\f -> (sapp (sapp (svar f) (shole hole1) sTHole) (shole hole2) sTHole)))
