module TypeCraft.Purescript.Alpha where

import Data.Map as Map

import Prelude
import Prim hiding (Type)

import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Unification (applySubChange, applySubType, Sub)
import Data.Map as Map
import Data.List as List
import TypeCraft.Purescript.MD (defaultTNeuMD)
import Data.Tuple.Nested
import Effect.Exception.Unsafe (unsafeThrow)

{-
This file deals with issues of alpha-equivalence.
The is irrelvant for terms, since we never compare terms for equality.
Instead, it is relevant for PolyTypes, and PolyChanges.
-}

{-
Conventions:
In a function which inputs two PolyTypes or PolyChanges,
the TypeVarID's on the left input get mapped to corresponding TypeVarID's on the right input.
-}
type TyVarEquiv = Map.Map TypeVarID TypeVarID

--instance eqPolyType :: Eq PolyType where
--        eq pt1 pt2 = polyTypeEqImpl Map.empty pt1 pt2

polyTypeEq :: PolyType -> PolyType -> Boolean
polyTypeEq pt1 pt2 = polyTypeEqImpl Map.empty pt1 pt2

polyTypeEqImpl :: TyVarEquiv -> PolyType -> PolyType -> Boolean
polyTypeEqImpl equiv (Forall x pt1) (Forall y pt2) = polyTypeEqImpl (Map.insert x y equiv) pt1 pt2
polyTypeEqImpl equiv (PType ty1) (PType ty2) = (subType equiv ty1) == ty2
polyTypeEqImpl _ _ _ = false

subType :: TyVarEquiv -> Type -> Type
subType equiv = applySubType { subTypeVars : (map (\x -> TNeu defaultTNeuMD x List.Nil) equiv) , subTHoles : Map.empty}

subChange :: TyVarEquiv -> Change -> Change
subChange equiv = applySubChange { subTypeVars : (map (\x -> TNeu defaultTNeuMD x List.Nil) equiv) , subTHoles : Map.empty}

subChangeParam :: TyVarEquiv -> ChangeParam -> ChangeParam
subChangeParam equiv (ChangeParam c) = ChangeParam (subChange equiv c)
subChangeParam equiv (PlusParam t) = PlusParam (subType equiv t)
subChangeParam equiv (MinusParam t) = MinusParam (subType equiv t)

subTypeArg :: TyVarEquiv -> TypeArg -> TypeArg
subTypeArg equiv (TypeArg md ty) = TypeArg md (subType equiv ty)

polyTypeApply :: PolyType -> List.List TypeArg -> Type
polyTypeApply pty args =
    let sub /\ ty = polyTypeImpl pty args in
    applySubType {subTypeVars: sub, subTHoles: Map.empty} ty
polyTypeImpl :: PolyType -> List.List TypeArg -> Map.Map TypeVarID Type /\ Type
polyTypeImpl (Forall x pt) ((TypeArg _ ty) List.: args) =
    let sub /\ ty = polyTypeImpl pt args in
    Map.insert x ty sub /\ ty
polyTypeImpl (PType ty) List.Nil = Map.empty /\ ty
polyTypeImpl _ _ = unsafeThrow "in polyTypeApply, wrong number of args"

--data PolyType = Forall TypeVarID PolyType | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.
