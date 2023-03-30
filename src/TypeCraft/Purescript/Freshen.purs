module TypeCraft.Purescript.Freshen where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar

import Data.List (List(..), foldr, (:))
import Data.Map.Internal (Map, insert, empty, lookup, member)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.MD (defaultTNeuMD)
import TypeCraft.Purescript.Util (lookup', mapKeys, union')

{-
This file has functions which traverse over various pieces of the grammar and freshen the variables.
Nothing interesting is happening here, but it sure is a lot of code...
I still don't think that debruin indices would save development time without an intrisically typed DSL
in dependent type theory to catch off-by-one errors.
-}

--freshenChange :: Change -> Change
--freshenChange c = fst (freshenChangeImpl empty c)
--
--freshenChangeImpl :: Map TypeHoleID TypeHoleID -> Change -> Change /\ Map TypeHoleID TypeHoleID
--freshenChangeImpl m (CArrow c1 c2) =
--    let c1' /\ m' = freshenChangeImpl m c1 in
--    let c2' /\ m'' = freshenChangeImpl m' c2 in
--    CArrow c1 c2 /\ m''
--freshenChangeImpl m (CNeu x args) =
--    let args' /\ m' = freshenChangeParams m args in
--    (CNeu x args') /\ m'
--freshenChangeImpl m (CHole x) =
--    case lookup x m of
--    Just y -> CHole y /\ m
--    Nothing -> let y = freshTypeHoleID unit in
--        CHole y /\ insert x y m
--freshenChangeImpl m (Plus t c) =
--    let t' /\ m' = freshenTypeImpl m t in
--    let c' /\ m'' = freshenChangeImpl m' c in
--    Plus t' c' /\ m''
--freshenChangeImpl m (Minus t c) =
--    let t' /\ m' = freshenTypeImpl m t in
--    let c' /\ m'' = freshenChangeImpl m' c in
--    Minus t' c' /\ m''
--freshenChangeImpl m (Replace a b) =
--    let a' /\ m' = freshenTypeImpl m a in
--    let b' /\ m'' = freshenTypeImpl m' b in
--    Replace a' b' /\ m''
--
--freshenChangeParams :: Map TypeHoleID TypeHoleID -> List ChangeParam -> List ChangeParam /\ Map TypeHoleID TypeHoleID
--freshenChangeParams m Nil = Nil /\ m
--freshenChangeParams m (ChangeParam c : params) =
--    let c' /\ m' = freshenChangeImpl m c in
--    let params' /\ m'' = freshenChangeParams m' params in
--    (ChangeParam c' : params') /\ m''
--freshenChangeParams m (PlusParam t : params) =
--    let t' /\ m' = freshenTypeImpl m t in
--    let params' /\ m'' = freshenChangeParams m' params in
--    (PlusParam t' : params') /\ m''
--freshenChangeParams m (MinusParam t : params) =
--    let t' /\ m' = freshenTypeImpl m t in
--    let params' /\ m'' = freshenChangeParams m' params in
--    (MinusParam t' : params') /\ m''
--
--freshenTypeImpl :: Map TypeHoleID TypeHoleID -> Type -> Type /\ Map TypeHoleID TypeHoleID
--freshenTypeImpl m (Arrow md c1 c2) =
--    let c1' /\ m' = freshenTypeImpl m c1 in
--    let c2' /\ m'' = freshenTypeImpl m' c2 in
--    Arrow md c1 c2 /\ m''
--freshenTypeImpl m (TNeu md x args) =
--    let args' /\ m' = foldr (\ (TypeArg md t) (args' /\ m) ->
--        let t' /\ m' = freshenTypeImpl m t in
--        ((TypeArg md t') : args') /\ m') (Nil /\ m) args
--    in (TNeu md x args') /\ m'
--freshenTypeImpl m (THole md x) =
--    case lookup x m of
--    Just y -> THole md y /\ m
--    Nothing -> let y = freshTypeHoleID unit in
--        THole md y /\ insert x y m

type TyVarSub = Map TypeVarID TypeVarID
type TyVarEquiv = Map.Map TypeVarID TypeVarID
genFreshener :: List TypeVarID -> TyVarSub
genFreshener Nil = empty
genFreshener (x : xs) = insert x (freshTypeVarID unit ) (genFreshener xs)

--freshenTyBinds :: List TypeBind -> List TypeBind /\ TyVarFreshener
--freshenTyBinds Nil = Nil /\ empty
--freshenTyBinds (tyBind : tyBinds) =
--    let freshener
--subTypeBind :: TyVarSub -> TypeBind -> TypeBind
--subTypeBind sub (TypeBind md x) = TypeBind md (lookup' x sub)

--subTypeArg :: TyVarSub -> TypeArg -> TypeArg
--subTypeArg sub (TypeArg md ty) = TypeArg md (subType sub ty)

--subType :: TyVarSub -> Type -> Type
--subType sub (Arrow md t1 t2) = Arrow md (subType sub t1) (subType sub t2)
---- subType sub (THole md x w s) = THole md x w (union' s (map makeTHole ?sub)) -- TODO: is there an issue with the THoles made from sub not themselves having subs on them???
--subType sub (THole md x w s) = THole md x w (union' s ((\typeVarId -> TNeu defaultTNeuMD (TypeVar typeVarId) Nil) <$> sub)) -- TODO: is there an issue with the THoles made from sub not themselves having subs on them???
--subType sub (TNeu md x tys) = TNeu md (subTypeVar sub x) (map (subTypeArg sub) tys)

--subTypeVarID :: TyVarSub -> TypeVarID -> TypeVarID
--subTypeVarID sub x = case lookup x sub of
--    Nothing -> x
--    Just y -> y
--
--subTypeVar :: TyVarSub -> TypeVar -> TypeVar
--subTypeVar sub (TypeVar x) = TypeVar (lookup' x sub)
--subTypeVar sub (CtxBoundaryTypeVar pt mtv name x) =
--    if member x sub then unsafeThrow "I don't think that this should be in scope " else
--    CtxBoundaryTypeVar pt mtv name x

--subCtrParam :: TyVarSub -> CtrParam -> CtrParam
--subCtrParam sub (CtrParam md ty) = CtrParam md (subType sub ty)

--subConstructor :: TyVarSub -> Constructor -> Constructor
--subConstructor sub (Constructor md tBind ctrParams) = Constructor md tBind (map (subCtrParam sub) ctrParams)

--------------------------------------------------------------------------------
--RENAMING
--------------------------------------------------------------------------------
renType :: TyVarEquiv -> Type -> Type
renType ren (Arrow md t1 t2) = Arrow md (renType ren t1) (renType ren t2)
renType ren (THole md x w s) = THole md x w (map (\(name /\ ty) -> name /\ renType ren ty) s)
renType ren (TNeu md tv tyArgs) = TNeu md tv (map (\(TypeArg md ty) -> TypeArg md (renType ren ty)) tyArgs)

renSubChange :: TyVarEquiv -> SubChange -> SubChange
renSubChange ren (SubTypeChange name1 name2 ch) = SubTypeChange name1 name2 (renChange ren ch)
renSubChange ren (SubInsert name ty) = SubInsert name (renType ren ty)
renSubChange ren (SubDelete name ty) = SubDelete name (renType ren ty)

{-
Question: is renaming not a special case of substitution because of hole subs?
In other words, applying the substitution [x/y] to ? yields ?[x/y],
while applying the renaming [x/y] to ? yields ?
-}
renChange :: TyVarEquiv -> Change -> Change
renChange ren (CArrow c1 c2) = CArrow (renChange ren c1) (renChange ren c2)
renChange ren (CHole x w s) = CHole x w (map (renSubChange ren) s)
renChange ren (Replace t1 t2) = Replace (renType ren t1) (renType ren t2)
renChange ren (Plus t c) = Plus (renType ren t) (renChange ren c)
renChange ren (Minus t c) = Minus (renType ren t) (renChange ren c)
renChange ren (CNeu tv chParams) = CNeu tv (map (renChangeParam ren) chParams)
--data Change
--  = CArrow Change Change
--  | CHole TypeHoleID (Set TypeVarID) (Map TypeVarID SubChange)
--  | Replace Type Type
--  | Plus Type Change
--  | Minus Type Change
--  | CNeu CTypeVar (List ChangeParam)
--data Type
--  = Arrow ArrowMD Type Type
--  | THole THoleMD TypeHoleID {-Weakenings-} (Set TypeVarID) {-Substitutions-} (Map TypeVarID Type)
--  | TNeu TNeuMD TypeVar (List TypeArg)

renChangeParam :: TyVarEquiv -> ChangeParam -> ChangeParam
renChangeParam ren (ChangeParam c) = ChangeParam (renChange ren c)
renChangeParam ren (PlusParam t) = PlusParam (renType ren t)
renChangeParam ren (MinusParam t) = MinusParam (renType ren t)

renCtrParam :: TyVarEquiv -> CtrParam -> CtrParam
renCtrParam sub (CtrParam md ty) = CtrParam md (renType sub ty)
