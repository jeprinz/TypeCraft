module TypeCraft.Purescript.Alpha where

import Data.Map as Map

import Prelude
import Prim hiding (Type)

import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (lookup')
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.List ((:))
import TypeCraft.Purescript.MD (defaultTNeuMD)
import Data.Tuple.Nested
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Maybe (maybe)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (union')
import TypeCraft.Purescript.TypeChangeAlgebra2
import Data.Tuple (fst, snd)
import Data.Maybe (Maybe(..))
import Debug (trace)
import Data.Foldable (foldl)

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

convertSub :: TyVarEquiv -> Sub
convertSub equiv = { subTypeVars : (map (\x -> TNeu defaultTNeuMD (TypeVar x) List.Nil) equiv) , subTHoles : Map.empty}

subType :: TyVarEquiv -> Type -> Type
subType equiv = applySubType { subTypeVars : (map (\x -> TNeu defaultTNeuMD (TypeVar x) List.Nil) equiv) , subTHoles : Map.empty}

renType :: TyVarEquiv -> Type -> Type
renType ren (Arrow md t1 t2) = Arrow md (renType ren t1) (renType ren t2)
renType ren (THole md x w s) = THole md x w (map (renType ren) s)
renType ren (TNeu md tv tyArgs) = TNeu md tv (map (\(TypeArg md ty) -> TypeArg md (renType ren ty)) tyArgs)

renSubChange :: TyVarEquiv -> SubChange -> SubChange
renSubChange ren (SubTypeChange ch) = SubTypeChange (renChange ren ch)
renSubChange ren (SubInsert ty) = SubInsert (renType ren ty)
renSubChange ren (SubDelete ty) = SubDelete (renType ren ty)

renChange :: TyVarEquiv -> Change -> Change
renChange ren (CArrow c1 c2) = CArrow (renChange ren c1) (renChange ren c2)
renChange ren (CHole x w s) = CHole x w (map (renSubChange ren) s)
renChange ren (Replace t1 t2) = Replace (renType ren t1) (renType ren t2)
renChange ren (Plus t c) = Plus (renType ren t) (renChange ren c)
renChange ren (Minus t c) = Minus (renType ren t) (renChange ren c)
renChange ren (CNeu tv chParams) = CNeu tv (map (renChangeParam ren) chParams)

renChangeParam :: TyVarEquiv -> ChangeParam -> ChangeParam
renChangeParam ren (ChangeParam c) = ChangeParam (renChange ren c)
renChangeParam ren (PlusParam t) = PlusParam (renType ren t)
renChangeParam ren (MinusParam t) = MinusParam (renType ren t)

--subTypeArg :: TyVarEquiv -> TypeArg -> TypeArg
--subTypeArg equiv (TypeArg md ty) = TypeArg md (subType equiv ty)

polyTypeApply :: PolyType -> List.List TypeArg -> Type
polyTypeApply pty args =
    let sub /\ ty = polyTypeImpl pty args in
    applySubType {subTypeVars: sub, subTHoles: Map.empty} ty
polyTypeImpl :: PolyType -> List.List TypeArg -> Map.Map TypeVarID Type /\ Type
polyTypeImpl (Forall x pt) ((TypeArg _ arg) List.: args) =
    let sub /\ ty = polyTypeImpl pt args in
    Map.insert x arg sub /\ ty
polyTypeImpl (PType ty) List.Nil = Map.empty /\ ty
polyTypeImpl _ _ = unsafeThrow "in polyTypeApply, wrong number of args"

--data PolyType = Forall TypeVarID PolyType | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.

--------------------------------------------------------------------------------
--------- Substitution ---------------------------------------------------------
--------------------------------------------------------------------------------

type Sub
  = { subTypeVars :: Map.Map TypeVarID Type
    , subTHoles :: Map.Map TypeHoleID Type
    }

subFromVars :: Map.Map TypeVarID Type -> Sub
subFromVars m = {subTypeVars: m, subTHoles: Map.empty}

{-
The input Sub goes from a starting context to an ending context. We need the output type to be in that ending context.
When we apply to sub to a hole, we need to add the sub to the subs on that hole, because the hole is a metavariable that lives
in a different context.
We can assume that everything in the input Type is in the starting context.
But the subs in the holes are themselves
-}
applySubType :: Sub -> Type -> Type
applySubType sub = case _ of
  Arrow md ty1 ty2 -> Arrow md (applySubType sub ty1) (applySubType sub ty2)
  (THole md hid w s) -> maybe (THole md hid w (union' (map (applySubType sub) s) sub.subTypeVars)) (applySubType (subFromVars s)) (Map.lookup hid sub.subTHoles) -- TODO: is union' correct here?
  ty@(TNeu md (TypeVar id) List.Nil) -> maybe ty identity (Map.lookup id sub.subTypeVars)
  TNeu md id args -> TNeu md id ((\(TypeArg md ty) -> TypeArg md (applySubType sub ty)) <$> args)

subTypeArg :: Sub -> TypeArg -> TypeArg
subTypeArg sub (TypeArg md ty) = TypeArg md (applySubType sub ty)

subSubChange :: Sub -> SubChange -> SubChange
subSubChange sub subChange =
    case subChange of
        SubTypeChange ch -> SubTypeChange (applySubChange sub ch)
        SubDelete ty -> SubDelete (applySubType sub ty)
        SubInsert ty -> SubInsert (applySubType sub ty)

-- Whereas a Sub goes from one context to anotoher, a CSub goes from one change context to another.
-- Thus, if it goes from a change context with - x : C to one with + x : C
-- We need substitutions that looks like +[x/C] or -[x/T]
-- Here we're talking about substitutions which make the context shorter; they only remove variables by substituting them away.
-- Thus, there is no question of whether a given variable is + or - in the output context: it is either removed, or stays the same.
type CSub
  = { subTypeVars :: Map.Map TypeVarID SubChange
    , subTHoles :: Map.Map TypeHoleID Change
    }

getCSubEndpoints :: CSub -> Sub /\ Sub
getCSubEndpoints {subTypeVars , subTHoles} =
    let subTypeVars1 /\ subTypeVars2 = getSubEndpoints subTypeVars in
    let subTHoles' = map getEndpoints subTHoles in
    let subTHoles1 = map fst subTHoles' in
    let subTHoles2 = map snd subTHoles' in
    {subTypeVars: subTypeVars1, subTHoles: subTHoles1}
    /\ {subTypeVars: subTypeVars2, subTHoles: subTHoles2}

subSubChangeGen :: CSub -> SubChange -> SubChange
subSubChangeGen sub subChange =
    case subChange of
        SubTypeChange ch -> SubTypeChange (applySubChangeGen sub ch)
        SubDelete ty -> SubDelete (applySubType (fst (getCSubEndpoints sub)) ty)
        SubInsert ty -> SubInsert (applySubType (snd (getCSubEndpoints sub)) ty)

--data CTypeVar = CTypeVar TypeVarID | CCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID
--    | PlusCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID
--    | MinusCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID
subCTypeVarGen :: CSub -> CTypeVar -> Maybe Change
subCTypeVarGen sub (CTypeVar x) = case Map.lookup x sub.subTypeVars of
    Just (SubTypeChange c) -> Just c
    Just (SubDelete t) ->
--        Just $ Replace (TNeu defaultTNeuMD (TypeVar x) List.Nil) t
        Just $ Replace t (TNeu defaultTNeuMD (TypeVar x) List.Nil)
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 1"
subCTypeVarGen sub (CCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
    Just _ -> unsafeThrow "shouldn't happen subCTypeVarGen 5"
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 2"
subCTypeVarGen sub (PlusCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
   Just (SubDelete t) -> Just $ Replace t (TNeu defaultTNeuMD (CtxBoundaryTypeVar k mtv name x) List.Nil)
   Nothing -> Nothing
   _ -> unsafeThrow "shouldn't happen subCTypeVarGen 3"
subCTypeVarGen sub (MinusCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
    Just (SubInsert t) -> Just $ Replace (TNeu defaultTNeuMD (CtxBoundaryTypeVar k mtv name x) List.Nil) t
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 4"

applySubChangeGen :: CSub -> Change -> Change
applySubChangeGen sub ch =
--  trace ("applySubChangeGen called. ch is: " <> show ch) \_ ->
  case ch of
  CArrow ty1 ty2 -> CArrow (applySubChangeGen sub ty1) (applySubChangeGen sub ty2)
  (CHole hid w s) -> maybe (\_ -> CHole hid w (union' (map (subSubChangeGen sub) s) sub.subTypeVars))
        (\c _ -> applySubChangeGen {subTHoles: Map.empty, subTypeVars: s} c)
        (Map.lookup hid sub.subTHoles) unit
  ty@(CNeu tv List.Nil) -> maybe ty identity (subCTypeVarGen sub tv) -- NOTE: if I ever do a substitution in cases other than when args are Nil, then I need to fix subCTypeVarGen to accomodate that.
  CNeu id args -> CNeu id (applySubChangeParamGen sub <$> args)
  Replace ty1 ty2 ->
    let sub1 /\ sub2 = getCSubEndpoints sub in -- Does this make sense? Can typechanges go from one context to another? So the left part of the replace is in the starting context, while the right part is in the ending context?
    Replace (applySubType sub1 ty1) (applySubType sub2 ty2)
  Plus ty ch -> Plus (applySubType (snd (getCSubEndpoints sub)) ty) (applySubChangeGen sub ch)
  Minus ty ch -> Minus (applySubType (fst (getCSubEndpoints sub)) ty) (applySubChangeGen sub ch)
applySubChangeParamGen :: CSub -> ChangeParam -> ChangeParam
applySubChangeParamGen sub = case _ of
    ChangeParam ch -> ChangeParam (applySubChangeGen sub ch)
    PlusParam ty -> PlusParam (applySubType (snd (getCSubEndpoints sub)) ty)
    MinusParam ty -> MinusParam (applySubType (fst (getCSubEndpoints sub)) ty)

-- TODO TODO TODO: replace the implementation of applySubChange with a call to applySubChangeGen with the appropriate injections on sub.
-- But I kind of want to wait until we have some unit tests before I do that...
applySubChange :: Sub -> Change -> Change
applySubChange sub ch =
--    trace ("in applySubChange, sub is: " <> show sub <> " and ch is: " <> show ch) \_ ->
    let res = applySubChangeGen {subTypeVars: map (SubTypeChange <<< tyInject) sub.subTypeVars, subTHoles: map tyInject sub.subTHoles} ch in
--    trace ("and now were done with applySubChange") \_ ->
    res
--applySubChange sub = case _ of
--  CArrow ty1 ty2 -> CArrow (applySubChange sub ty1) (applySubChange sub ty2)
----  ty@(CHole hid w s) -> maybe (CHole hid w ?h ) (\t -> tyInjectWithSub (subSubChange (subFromVars s) t)) (Map.lookup hid sub.subTHoles)
--  ty@(CHole hid w s) -> maybe (CHole hid w (map (subSubChange sub) s))
--        (\t ->
--            let s1 /\ s2 = getSubEndpoints s in
--            Replace (applySubType (subFromVars s1) t) (applySubType (subFromVars s2) t))
--        (Map.lookup hid sub.subTHoles)
--  ty@(CNeu (CTypeVar id) List.Nil) -> maybe ty tyInject (Map.lookup id sub.subTypeVars)
--  CNeu id args -> CNeu id (applySubChangeParam sub <$> args)
--  Replace ty1 ty2 -> Replace (applySubType sub ty1) (applySubType sub ty2)
--  Plus ty ch -> Plus (applySubType sub ty) (applySubChange sub ch)
--  Minus ty ch -> Minus (applySubType sub ty) (applySubChange sub ch)
--applySubChangeParam :: Sub -> ChangeParam -> ChangeParam
--applySubChangeParam sub = case _ of
--    ChangeParam ch -> ChangeParam (applySubChange sub ch)
--    PlusParam ty -> PlusParam (applySubType sub ty)
--    MinusParam ty -> MinusParam (applySubType sub ty)

emptySub :: Sub
emptySub = { subTypeVars: Map.empty, subTHoles: Map.empty }

subTerm :: Sub -> Term -> Term
subTerm sub term =
    let rec = subTerm sub in
    let st = applySubType sub in
    case term of
    App md t1 t2 argTy outTy -> App md (rec t1) (rec t2) (st argTy) (st outTy)
    Lambda md tBind argTy body bodyTy -> Lambda md tBind (st argTy) (rec body) (st bodyTy)
    Var md x tyArgs -> Var md x (map (\(TypeArg md ty) -> TypeArg md (st ty)) tyArgs)
    Let md tBind tyBinds def defTy body bodyTy -> Let md tBind tyBinds (rec def) (st defTy) (rec body) (st bodyTy)
    Data md tyBind tyBinds ctrs body bodyTy -> Data md tyBind tyBinds (map (subConstructor sub) ctrs) (rec body) (st bodyTy)
    TLet md tyBind tyBinds def body bodyTy -> TLet md tyBind tyBinds (st def) (rec body) (st bodyTy)
    TypeBoundary md ch body -> TypeBoundary md (applySubChange sub ch) (rec body)
    ContextBoundary md x ch body -> ContextBoundary md x (subVarChange sub ch) (rec body)
    Hole md -> Hole md
    Buffer md def defTy body bodyTy -> Buffer md (rec def) (st defTy) (rec body) (st bodyTy)

typeContainsVar :: Set.Set TypeVarID -> Type -> Boolean
typeContainsVar vars (Arrow md t1 t2) = (typeContainsVar vars t1) || (typeContainsVar vars t2)
typeContainsVar vars (THole md x w s) = (List.any (typeContainsVar vars) s)
typeContainsVar vars (TNeu md tv tyArgs) = typeVarContainsVar vars tv || (List.any (\(TypeArg md ty) -> (typeContainsVar vars ty)) tyArgs)

typeVarContainsVar :: Set.Set TypeVarID -> TypeVar -> Boolean
typeVarContainsVar vars (TypeVar x) = Set.member x vars
typeVarContainsVar vars (CtxBoundaryTypeVar _ _ _ x) = Set.member x vars

typeContainsHoles :: Set.Set TypeHoleID -> Type -> Boolean
typeContainsHoles holes (Arrow md t1 t2) = (typeContainsHoles holes t1) || (typeContainsHoles holes t2)
typeContainsHoles holes (THole md x w s) = (Set.member x holes) || (List.any (typeContainsHoles holes) s)
typeContainsHoles holes (TNeu md tv tyArgs) = (List.any (\(TypeArg md ty) -> (typeContainsHoles holes ty)) tyArgs)

tyVarsUsedInType :: Type -> Set.Set TypeVarID
tyVarsUsedInType (Arrow md t1 t2) = Set.union (tyVarsUsedInType t1) (tyVarsUsedInType t2)
tyVarsUsedInType (THole md x w s) = List.foldl (\holes ty -> Set.union holes (tyVarsUsedInType ty)) Set.empty s
tyVarsUsedInType (TNeu md tv tyArgs) = Set.insert (tyVarGetID tv) (List.foldl (\holes (TypeArg md ty) -> Set.union holes (tyVarsUsedInType ty)) Set.empty tyArgs)

tyVarGetID :: TypeVar -> TypeVarID
tyVarGetID (TypeVar x) = x
tyVarGetID (CtxBoundaryTypeVar _ _ _ x) = x

subChangeContainsHoles :: Set.Set TypeHoleID -> SubChange -> Boolean
subChangeContainsHoles holes (SubTypeChange ch) = changeContainsHoles holes ch
subChangeContainsHoles holes (SubInsert ty) = typeContainsHoles holes ty
subChangeContainsHoles holes (SubDelete ty) = typeContainsHoles holes ty

changeContainsHoles :: Set.Set TypeHoleID -> Change -> Boolean
changeContainsHoles holes (CArrow c1 c2) = changeContainsHoles holes c1 || changeContainsHoles holes c2
changeContainsHoles holes (CHole x w s) = Set.member x holes || List.any (subChangeContainsHoles holes) s
changeContainsHoles holes (Replace t1 t2) = typeContainsHoles holes t1 || typeContainsHoles holes t2
changeContainsHoles holes (Plus t c) = typeContainsHoles holes t || changeContainsHoles holes c
changeContainsHoles holes (Minus t c) = typeContainsHoles holes t || changeContainsHoles holes c
changeContainsHoles holes (CNeu tv chParams) = List.any (changeParamContainsHoles holes) chParams

polyChangeContainsHoles :: Set.Set TypeHoleID -> PolyChange -> Boolean
polyChangeContainsHoles holes (CForall _ pc) = polyChangeContainsHoles holes pc
polyChangeContainsHoles holes (PPlus _ pc) = polyChangeContainsHoles holes pc
polyChangeContainsHoles holes (PMinus _ pc) = polyChangeContainsHoles holes pc
polyChangeContainsHoles holes (PChange ch) = changeContainsHoles holes ch

polyTypeContainsHoles :: Set.Set TypeHoleID -> PolyType -> Boolean
polyTypeContainsHoles holes (Forall _ pt) = polyTypeContainsHoles holes pt
polyTypeContainsHoles holes (PType ch) = typeContainsHoles holes ch

varChangeContainsHoles :: Set.Set TypeHoleID -> VarChange -> Boolean
varChangeContainsHoles holes (VarTypeChange pc) = polyChangeContainsHoles holes pc
varChangeContainsHoles holes (VarDelete _ pt) = polyTypeContainsHoles holes pt
varChangeContainsHoles holes (VarInsert _ pt) = polyTypeContainsHoles holes pt

changeParamContainsHoles :: Set.Set TypeHoleID -> ChangeParam -> Boolean
changeParamContainsHoles holes (ChangeParam c) = changeContainsHoles holes c
changeParamContainsHoles holes (PlusParam t) = typeContainsHoles holes t
changeParamContainsHoles holes (MinusParam t) = typeContainsHoles holes t

ctrContainsHoles :: Set.Set TypeHoleID -> Constructor -> Boolean
ctrContainsHoles holes (Constructor _ _ ctrParams) = List.any (ctrParamContainsHoles holes) ctrParams

ctrParamContainsHoles :: Set.Set TypeHoleID -> CtrParam -> Boolean
ctrParamContainsHoles holes (CtrParam _ ty) = typeContainsHoles holes ty

termContainsHoles :: Set.Set TypeHoleID -> Term -> Boolean
termContainsHoles holes term =
    let rec = termContainsHoles holes in
    let st = typeContainsHoles holes in
    case term of
    App md t1 t2 argTy outTy -> rec t1 || rec t2 || st argTy || st outTy
    Lambda md tBind argTy body bodyTy -> st argTy || rec body || st bodyTy
    Var md x tyArgs -> (List.any (\(TypeArg md ty) -> st ty) tyArgs)
    Let md tBind tyBinds def defTy body bodyTy -> rec def || st defTy || rec body || st bodyTy
    Data md tyBind tyBinds ctrs body bodyTy -> (List.any (ctrContainsHoles holes) ctrs) || rec body || st bodyTy
    TLet md tyBind tyBinds def body bodyTy -> st def || rec body || st bodyTy
    TypeBoundary md ch body -> changeContainsHoles holes ch || rec body
    ContextBoundary md x ch body -> varChangeContainsHoles holes ch || rec body
    Hole md -> false
    Buffer md def defTy body bodyTy -> rec def || st defTy || rec body || st bodyTy

-- outputs true if substitution shouldn't' be allowed
{-
We need to check that no instance of the hole to be substituted appears above a binder of a TypeVarID appearing in that hole.
So we need to keep a running total of the set of typevars whose binders we have passed, and also a set of typevars which appear
in each hole.
- Each tooth we pass, we need to add to our set of out of scope typevars
- From our set of out of scope term holes, we compute a set of disallowed holes - those which reference typevars from that first set
- Each tooth, we need to check that no hole in that tooth is in that second set
-}
checkWeakeningViolationTermPath :: Map.Map TypeHoleID Type -> List.List Tooth -> Boolean
checkWeakeningViolationTermPath subIWantToMake path1 =
    let tyVarsEachHoleReferences = map tyVarsUsedInType subIWantToMake in
    let go :: Set.Set TypeHoleID -> List.List Tooth -> Boolean
        go badHoles path =
            case path of
                List.Nil -> false
                List.Cons tooth teeth ->
                    case checkHoleUsageTooth badHoles tooth of
                        Nothing -> true
                        Just newOutOfScopeTypeVars ->
                            let badHoles' = Set.union badHoles (Map.keys
                                (Map.filter
                                    (\refdVars -> not (Set.isEmpty (Set.intersection refdVars newOutOfScopeTypeVars))) -- check if set of vars has intersection with newOutOfScopeTypeVars
                                    tyVarsEachHoleReferences)) in
                            go badHoles' teeth
    in go Set.empty path1

-- returns true if sub shouldn't be allowed
checkWeakeningViolationTypePath :: Map.Map TypeHoleID Type -> List.List Tooth -> Boolean
checkWeakeningViolationTypePath _subIWantToMake List.Nil = false
checkWeakeningViolationTypePath subIWantToMake (tooth : teeth) =
    case tooth of
        Lambda2 md tBind {--} body bodyTy -> checkWeakeningViolationTermPath subIWantToMake teeth
        Let4 md tBind tyBinds def {-defTy-} body bodyTy -> checkWeakeningViolationTermPath subIWantToMake teeth
        Buffer2 md def {-defTy-} body bodyTy -> checkWeakeningViolationTermPath subIWantToMake teeth
        TLet3 md tyBind tyBinds {-def-} body bodyTy -> checkWeakeningViolationTermPath subIWantToMake teeth
        Arrow1 md {--} ty2 -> checkWeakeningViolationTypePath subIWantToMake teeth
        Arrow2 md ty1 {--} -> checkWeakeningViolationTypePath subIWantToMake teeth
        TypeArg1 md {--} -> checkWeakeningViolationTypeArgPath subIWantToMake teeth
        _ -> unsafeThrow ("Either wasn't a type path, or I forgot a case in checkWeakeningViolationTypePath. tooth was: " <> show tooth)

checkWeakeningViolationTypeArgPath :: Map.Map TypeHoleID Type -> UpPath -> Boolean
checkWeakeningViolationTypeArgPath _subIWantToMake List.Nil = false
checkWeakeningViolationTypeArgPath subIWantToMake (tooth : teeth) =
--    trace ("Here I am. tooth is:" <> show tooth <> "\n and teeth is: " <> show teeth) \_ ->
    case tooth of
        TypeArgListCons1 {--} tyArgs -> checkWeakeningViolationTypeArgListPath subIWantToMake teeth
        _ -> unsafeThrow ("Either wasn't a TypeArg path, or I forgot a case in checkWeakeningViolationTypeArgPath. tooth was: " <> show tooth)

checkWeakeningViolationTypeArgListPath :: Map.Map TypeHoleID Type -> UpPath -> Boolean
checkWeakeningViolationTypeArgListPath sub List.Nil = false
checkWeakeningViolationTypeArgListPath sub (tooth : teeth) =
    case tooth of
        TypeArgListCons2 tyArg -> checkWeakeningViolationTypeArgListPath sub teeth
        TNeu1 md x {--} -> checkWeakeningViolationTypePath sub teeth
        Var1 md x {-List TypeArg-} -> checkWeakeningViolationTermPath sub teeth
        _ -> unsafeThrow ("Either wasn't a TypeArgList path, or I forgot a case in checkWeakeningViolationTypeArgListPath. tooth was: " <> show tooth)


checkHoleUsageTooth :: Set.Set TypeHoleID -> Tooth -> Maybe (Set.Set TypeVarID)
checkHoleUsageTooth holes tooth =
    let term = termContainsHoles holes in
    let ty = typeContainsHoles holes in
    case tooth of
        App1 md {-Term-} t2 argTy bodyTy -> if term t2 || ty argTy || ty bodyTy then Nothing else Just Set.empty
        App2 md t1 {-Term-} argTy bodyTy -> if term t1 || ty argTy || ty bodyTy then Nothing else Just Set.empty
        Lambda3 md tBind argTy {-Term-} bodyTy -> if ty argTy || ty bodyTy then Nothing else Just Set.empty
        Let3 md tBind tyBinds {-Term-} defTy body bodyTy ->
            if ty defTy || term body || ty bodyTy then Nothing else
            Just (Set.fromFoldable (map (\(TypeBind _ ty) -> ty) tyBinds))
        Let5 md tBind tyBinds def defTy {-Term-} bodyTy -> if term def || ty defTy || ty bodyTy then Nothing else Just Set.empty
        Buffer1 md {-Term-} defTy body bodyTy -> if ty defTy || term body || ty bodyTy then Nothing else Just Set.empty
        Buffer3 md def defTy {-Term-} bodyTy -> if term def || ty defTy || ty bodyTy then Nothing else Just Set.empty
        TypeBoundary1 md ch {-Term-} -> if changeContainsHoles holes ch then Nothing else Just Set.empty
        ContextBoundary1 md x vch {-Term-} -> if varChangeContainsHoles holes vch then Nothing else Just Set.empty
        TLet4 md tyBind tyBinds def {-Term-} bodyTy -> unsafeThrow "no"
        Data4 md (TypeBind _ x) tyBinds ctrs {-Term-} bodyTy -> if List.any (ctrContainsHoles holes) ctrs || ty bodyTy then Nothing else Just
            (Set.singleton x)
        _ -> unsafeThrow ("Either wasn't a term tooth, or I forgot a case in checkHoleUsageTooth. tooth is: " <> show tooth)

subTermPath :: Sub -> UpPath -> UpPath
subTermPath sub List.Nil = List.Nil
subTermPath sub (tooth List.: rest) = (subTermTooth sub tooth) List.: (subTermPath sub rest)

subTermTooth :: Sub -> Tooth -> Tooth
subTermTooth sub tooth =
    let rec = subTerm sub in
    let st = applySubType sub in
    case tooth of
        App1 md {-Term-} t2 argTy bodyTy -> App1 md (rec t2) (st argTy) (st bodyTy)
        App2 md t1 {-Term-} argTy bodyTy -> App2 md (rec t1) (st argTy) (st bodyTy)
        Lambda3 md tBind argTy {-Term-} bodyTy -> Lambda3 md tBind (st argTy) (st bodyTy)
        Let3 md tBind tyBinds {-Term-} defTy body bodyTy -> Let3 md tBind tyBinds (st defTy) (rec body) (st bodyTy)
        Let5 md tBind tyBinds def defTy {-Term-} bodyTy -> Let5 md tBind tyBinds (rec def) (st defTy) (st bodyTy)
        Buffer1 md {-Term-} defTy body bodyTy -> Buffer1 md (st defTy) (rec body) (st bodyTy)
        Buffer3 md def defTy {-Term-} bodyTy -> Buffer3 md (rec def) (st defTy) (st bodyTy)
        TypeBoundary1 md ch {-Term-} -> TypeBoundary1 md (applySubChange sub ch)
        ContextBoundary1 md x vch {-Term-} -> ContextBoundary1 md x (subVarChange sub vch)
        TLet4 md tyBind tyBinds def {-Term-} bodyTy -> TLet4 md tyBind tyBinds (st def) (st bodyTy)
        Data4 md tyBind tyBinds ctrs {-Term-} bodyTy -> Data4 md tyBind tyBinds (map (subConstructor sub) ctrs) (st bodyTy)
        _ -> unsafeThrow "Either wasn't a term tooth, or I forgot a case in subTermTooth"

subInsideHolePath :: Sub -> UpPath -> UpPath
subInsideHolePath sub ((Hole1 md) List.: rest) = Hole1 md List.: (subTermPath sub rest)
subInsideHolePath _ _ = unsafeThrow "in subInsideHolePath, wasn't a valid InsideHolePath"

--Need subTypeTooth as well...
--
--
--Lambda2 LambdaMD TermBind {-Type-} Term Type
--Let4 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
--Buffer2 BufferMD Term {-Type-} Term Type
--TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
--Arrow1 ArrowMD {-Type-} Type
--Arrow2 ArrowMD Type {-Type-}
--TypeArg1 TypeArgMD {-Type-}
--
--
--TNeu1 TNeuMD TypeVarID {-List TypeArg-}
--TypeArgListCons2 (TypeArg) {-List TypeArg-}
--
--TypeArgListCons1 {-TypeArg-} (List TypeArg)

subTypePath :: Sub -> UpPath -> UpPath
subTypePath sub List.Nil = List.Nil
subTypePath sub (tooth : teeth) =
    let sterm = subTerm sub in
    let stype = applySubType sub in
    case tooth of
        Lambda2 md tBind {--} body bodyTy -> (Lambda2 md tBind {--} (sterm body) (stype bodyTy)) : subTermPath sub teeth
        Let4 md tBind tyBinds def {-defTy-} body bodyTy -> Let4 md tBind tyBinds (sterm def) {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        Buffer2 md def {-defTy-} body bodyTy -> Buffer2 md (sterm def) {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        TLet3 md tyBind tyBinds {-def-} body bodyTy -> TLet3 md tyBind tyBinds {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        Arrow1 md {--} ty2 -> Arrow1 md {--} (stype ty2) : subTypePath sub teeth
        Arrow2 md ty1 {--} -> Arrow2 md (stype ty1) {--} : subTypePath sub teeth
        TypeArg1 md {--} -> TypeArg1 md {--} : subTypeArgPath sub teeth
        _ -> unsafeThrow "Either wasn't a type path, or I forgot a case in subTypePath"

subTypeArgPath :: Sub -> UpPath -> UpPath
subTypeArgPath sub List.Nil = List.Nil
subTypeArgPath sub (tooth : teeth) =
    case tooth of
        TypeArgListCons1 {--} tyArgs -> TypeArgListCons1 {--} (map (subTypeArg sub) tyArgs) : subTypeArgListPath sub teeth
        _ -> unsafeThrow "Either wasn't a TypeArg path, or I forgot a case in subTypeArgPath"

subTypeArgListPath :: Sub -> UpPath -> UpPath
subTypeArgListPath sub List.Nil = List.Nil
subTypeArgListPath sub (tooth : teeth) =
    case tooth of
        TypeArgListCons2 tyArg -> TypeArgListCons2 (subTypeArg sub tyArg) : subTypeArgListPath sub teeth
        TNeu1 md x {--} -> TNeu1 md x : subTypePath sub teeth
        Var1 md x {-List TypeArg-} -> Var1 md x : subTermPath sub teeth
        _ -> unsafeThrow ("Either wasn't a TypeArgList path, or I forgot a case in subTypeArgListPath. tooth was: " <> show tooth)


subPolyChange :: Sub -> PolyChange -> PolyChange
subPolyChange sub polyChange =
    let rec = subPolyChange sub in
    case polyChange of
        CForall x pc -> CForall x (rec pc)
        PPlus x pc -> PPlus x (rec pc)
        PMinus x pc -> PMinus x (rec pc)
        PChange ch -> PChange (applySubChange sub ch)

subPolyType :: Sub -> PolyType -> PolyType
subPolyType sub = case _ of
  Forall x pt -> Forall x (subPolyType sub pt)
  PType ty -> PType (applySubType sub ty)


subVarChange :: Sub -> VarChange -> VarChange
subVarChange sub varChange =
    case varChange of
        VarTypeChange pc -> VarTypeChange (subPolyChange sub pc)
        VarDelete name pt -> VarDelete name (subPolyType sub pt)
        VarInsert name pt -> VarInsert name (subPolyType sub pt)

subConstructor :: Sub -> Constructor -> Constructor
subConstructor sub (Constructor md x ctrParams) = Constructor md x (map (subCtrParam sub) ctrParams)

subCtrParam :: Sub -> CtrParam -> CtrParam
subCtrParam sub (CtrParam md ty) = CtrParam md (applySubType sub ty)

subCtx :: Sub -> TermContext -> TermContext
subCtx sub ctx = map (subPolyType sub) ctx

subTACtx :: Sub -> TypeAliasContext -> TypeAliasContext
subTACtx sub actx = map (\(tyBinds /\ ty) -> tyBinds /\ applySubType sub ty) actx

-- Warning: this function doesn't map the keys!
subAllCtx :: Sub -> AllContext -> AllContext
subAllCtx sub ctxs = ctxs{ctx = subCtx sub ctxs.ctx, actx = subTACtx sub ctxs.actx}
