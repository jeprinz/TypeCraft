module TypeCraft.Purescript.Alpha where

import Data.Map as Map

import Prelude
import Prim hiding (Type)

import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Util (hole)

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
subType equiv (Arrow md ty1 ty2) = Arrow md (subType equiv ty1) (subType equiv ty2)
subType equiv (THole md x) = THole md x
subType equiv (TNeu md x args) = TNeu md (lookup' x equiv) (map (subTypeArg equiv) args)

subChange :: TyVarEquiv -> Change -> Change
subChange = hole unit

subTypeArg :: TyVarEquiv -> TypeArg -> TypeArg
subTypeArg equiv (TypeArg md ty) = TypeArg md (subType equiv ty)

--data PolyType = Forall TypeVarID PolyType | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.
