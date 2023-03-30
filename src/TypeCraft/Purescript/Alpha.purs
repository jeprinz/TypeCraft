module TypeCraft.Purescript.Alpha where

import Data.Map as Map

import Prelude
import Prim hiding (Type)

import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (lookup')
import Data.Map as Map
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
import TypeCraft.Purescript.Freshen (TyVarEquiv)

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


--subTypeArg :: TyVarEquiv -> TypeArg -> TypeArg
--subTypeArg equiv (TypeArg md ty) = TypeArg md (subType equiv ty)

polyTypeApply :: PolyType -> List.List TypeArg -> Type
polyTypeApply pty args =
    let sub /\ ty = polyTypeImpl pty args in
    applySubType {subTypeVars: sub, subTHoles: Map.empty} ty
polyTypeImpl :: PolyType -> List.List TypeArg -> Map.Map TypeVarID Type /\ Type
polyTypeImpl (Forall x name pt) ((TypeArg _ arg) List.: args) =
    let sub /\ ty = polyTypeImpl pt args in
    Map.insert x arg sub /\ ty
polyTypeImpl (PType ty) List.Nil = Map.empty /\ ty
polyTypeImpl _ _ = unsafeThrow "in polyTypeApply, wrong number of args"

--data PolyType = Forall TypeVarID PolyType | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.

--------------------------------------------------------------------------------
--------- Substitution ---------------------------------------------------------
--------------------------------------------------------------------------------

type Sub
  = { subTypeVars :: Map.Map TypeVarID (String /\ Type)
    , subTHoles :: Map.Map TypeHoleID Type
    }

subFromVars :: Map.Map TypeVarID (String /\ Type) -> Sub
subFromVars m = {subTypeVars: m, subTHoles: Map.empty}

applySubType :: Sub -> Type -> Type
applySubType sub = case _ of
  Arrow md ty1 ty2 -> Arrow md (applySubType sub ty1) (applySubType sub ty2)
  -- TODO: there is an issue with applying holes subs to a type with a hole that has subs with a hole in one if it's types, and then hole subs get added to that hole (what a sentence)
  (THole md hid w s) -> maybe (THole md hid w (union' (map (applySubType sub) s) sub.subTypeVars))
    (applySubType (subFromVars s)) (Map.lookup hid sub.subTHoles) -- TODO: is union' correct here?
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
--    let x = 1 + getSubEndpoints subTypeVars in
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
    Just (SubTypeChange name1 name2 c) -> Just c
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 1"
subCTypeVarGen sub (CCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
    Just _ -> unsafeThrow "shouldn't happen subCTypeVarGen 5"
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 2"
subCTypeVarGen sub (PlusCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
   Just (SubDelete name t) -> Just $ Replace t (TNeu defaultTNeuMD (CtxBoundaryTypeVar k mtv name x) List.Nil)
   Nothing -> Nothing
   _ -> unsafeThrow "shouldn't happen subCTypeVarGen 3"
subCTypeVarGen sub (MinusCtxBoundaryTypeVar k mtv name x) = case Map.lookup x sub.subTypeVars of
    Just (SubInsert name t) -> Just $ Replace (TNeu defaultTNeuMD (CtxBoundaryTypeVar k mtv name x) List.Nil) t
    Nothing -> Nothing
    _ -> unsafeThrow "shouldn't happen subCTypeVarGen 4"

applySubChangeGen :: CSub -> Change -> Change
applySubChangeGen sub = case _ of
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
    trace ("in applySubChange, sub is: " <> show sub <> " and ch is: " <> show ch) \_ ->
    let res = applySubChangeGen {subTypeVars: map (SubTypeChange <<< tyInject) sub.subTypeVars, subTHoles: map tyInject sub.subTHoles} ch in
    trace ("and now were done with applySubChange") \_ ->
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
        TNeu1 md x {--} -> TNeu1 md x : subTypeArgListPath sub teeth
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
        VarDelete pt -> VarDelete (subPolyType sub pt)
        VarInsert pt -> VarInsert (subPolyType sub pt)

subConstructor :: Sub -> Constructor -> Constructor
subConstructor sub (Constructor md x ctrParams) = Constructor md x (map (subCtrParam sub) ctrParams)

subCtrParam :: Sub -> CtrParam -> CtrParam
subCtrParam sub (CtrParam md ty) = CtrParam md (applySubType sub ty)

subCtx :: Sub -> TermContext -> TermContext
subCtx sub ctx = map (subPolyType sub) ctx

subTACtx :: Sub -> TypeAliasContext -> TypeAliasContext
subTACtx sub actx = map (\(tyBinds /\ ty) -> tyBinds /\ applySubType sub ty) actx

subAllCtx :: Sub -> AllContext -> AllContext
subAllCtx sub ctxs = ctxs{ctx = subCtx sub ctxs.ctx, actx = subTACtx sub ctxs.actx}
