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
import TypeCraft.Purescript.Util (hole')
import Control.Monad.State as State

{-
This file defines a shallow embedding to make it easier to write terms for testing purposes
-}

type CtxAndType = {kctx :: TypeContext, ctx :: TermContext, ty :: Type}

type STerm = CtxAndType -> Term
type SType = Type

slambda :: String -> (TermVarID -> STerm) -> STerm
slambda name body {kctx, ctx, ty: Arrow _ ty1 ty2} =
    let x = TermVarID $ unsafePerformEffect genUUID in
    let t = body x {kctx, ctx: insert x (PType ty1) ctx, ty: ty2} in
    Lambda defaultLambdaMD (TermBind {varName: name} x) ty1 t ty2
slambda _ _ _ = unsafeThrow "shouldn't happen slambda"

slet :: String -> Array TypeBind -> (TermVarID -> STerm) -> SType -> (TermVarID -> STerm) -> STerm
slet name tyPrms def defTy body {kctx, ctx, ty} =
    let x = TermVarID $ unsafePerformEffect genUUID in
    let defTy' = defTy in
    let ctx' = insert x (List.foldr (\(TypeBind _ y) -> Forall y) (PType defTy') tyPrms) ctx in
    let def' = def x {kctx, ctx: ctx', ty: defTy'} in
    let body' = body x {kctx, ctx: ctx', ty: ty} in
    Let defaultLetMD (TermBind {varName: name} x) (List.fromFoldable tyPrms) def' defTy' body' ty

slet' :: String -> (TermVarID -> STerm) -> SType -> (TermVarID -> STerm) -> STerm
slet' name def defTy body {kctx, ctx, ty} =
    let x = TermVarID $ unsafePerformEffect genUUID in
    let defTy' = defTy in
    let ctx' = insert x (PType defTy') ctx in
    let def' = def x {kctx, ctx: ctx', ty: defTy'} in
    let body' = body x {kctx, ctx: ctx', ty: ty} in
    Let defaultLetMD (TermBind {varName: name} x) Nil def' defTy' body' ty

sapp :: STerm -> SType -> STerm -> STerm
sapp t1 argTy t2 {kctx, ctx, ty} = let argTy' = argTy in
    App defaultAppMD (t1 {kctx, ctx, ty: Arrow defaultArrowMD argTy' ty}) (t2 {kctx, ctx, ty: argTy'}) argTy' ty

sHole :: STerm
sHole _ = Hole defaultHoleMD

sBindTHole :: forall a. (TypeHoleID -> a) -> a
sBindTHole bla = bla (freshTypeHoleID unit)

sTHole :: TypeHoleID -> SType
sTHole x = makeTHole x

sarrow :: SType -> SType -> SType
sarrow ty1 ty2 = Arrow defaultArrowMD ty1 ty2

sForall :: (Type -> PolyType) -> PolyType
sForall body = let x = freshTypeVarID unit in
    Forall x (body (TNeu defaultTNeuMD (TypeVar x) List.Nil))

type TyDefM = State.State AllContext
defTy :: Kind -> String -> TyDefM TypeVarID
defTy k name = do
    let id = freshTypeVarID unit
    _ <- State.modify (\ctxs -> ctxs{kctx = insert id k ctxs.kctx, mdkctx = insert id name ctxs.mdkctx})
    pure id

defTerm :: PolyType -> String -> TyDefM Unit
defTerm pty name = do
    let id = freshTermVarID unit
    _ <- State.modify (\ctxs -> ctxs{ctx = insert id pty ctxs.ctx, mdctx = insert id name ctxs.mdctx})
    pure unit

svar :: TermVarID -> STerm
svar x _ = Var defaultVarMD x Nil

program :: SType -> STerm -> Type /\ Term
program ty t = let ty' = ty in ty' /\ (t {kctx: empty, ctx: empty, ty: ty'})

--tyProgram :: SType -> Type
--tyProgram ty = ty {kctx: empty, ctx: empty}

exampleType1 :: Type
exampleType1 = freshTHole unit

--exampleTerm1 :: Term
--exampleTerm1 = program (
--    slambda "x" (\x -> svar x)
--    ) exampleType1

exampleProg1 :: Type /\ Term
exampleProg1 = 
    sBindTHole \hole1 -> program
        (sTHole hole1) 
        sHole


exampleProg2 :: Type /\ Term
exampleProg2 =
    sBindTHole \hole1 -> sBindTHole \hole2 -> sBindTHole \hole3 ->
        program (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
            (slambda "x" \x -> (slambda "y" \y -> sHole))

exampleProg3 :: Type /\ Term
exampleProg3 =
    sBindTHole \hole1 -> sBindTHole \hole2 -> sBindTHole \hole3 ->
        program (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
            (slambda "x" \x -> (slambda "y" \y -> svar x))

exampleProg4 :: Type /\ Term
exampleProg4 =
    sBindTHole \hole1 -> sBindTHole \hole2 -> sBindTHole \hole3 ->
        program (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
            (slet' "f" (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
                (\f -> svar f))

exampleProg5 :: Type /\ Term
exampleProg5 =
    sBindTHole \hole1 -> sBindTHole \hole2 -> sBindTHole \hole3 ->
        program (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
            (slet' "f" (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
                (\f -> (sapp (sapp (svar f) (sTHole hole1) sHole) (sTHole hole2) sHole)))

exampleProg6 :: Type /\ Term
exampleProg6 =
    sBindTHole \hole1 -> sBindTHole \hole2 -> sBindTHole \hole3 ->
        program (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
            (slet "f" [ TypeBind {varName: "A"} (TypeVarID $ unsafePerformEffect genUUID) ] (\f -> (slambda "x" \x -> (slambda "y" \y -> svar x)))
                (sarrow (sTHole hole1) (sarrow (sTHole hole2) (sTHole hole3)))
                (\f -> (sapp (sapp (svar f) (sTHole hole1) sHole) (sTHole hole2) sHole)))
