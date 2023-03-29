module TypeCraft.Purescript.SmallStep.Freshen where

import Prelude

import TypeCraft.Purescript.SmallStep.UTerm
import TypeCraft.Purescript.Alpha
import Data.Tuple.Nested
import Data.Map (Map)
import Data.Map as Map
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Freshen (TyVarSub, genFreshener)
import TypeCraft.Purescript.Util
import Data.Maybe (Maybe(..))
import Data.Maybe (maybe)
import Effect.Exception.Unsafe (unsafeThrow)
import Data.List (List(..), (:))


type TermVarSub = Map TermVarID TermVarID

genTermFreshener :: List TermVarID -> TermVarSub
genTermFreshener Nil = Map.empty
genTermFreshener (x : xs) = Map.insert x (freshTermVarID unit ) (genTermFreshener xs)

getTermVarID :: TermVarID -> TermVarSub -> TermVarID /\ TermVarSub
getTermVarID x sub = case Map.lookup x sub of
    Nothing -> let y = freshTermVarID unit in
        y /\ Map.insert x y sub
    Just _ -> unsafeThrow "shouldn't be in map yet"

getTypeVarID :: TypeVarID -> TyVarSub -> TypeVarID /\ TyVarSub
getTypeVarID x sub = case Map.lookup x sub of
    Nothing -> let y = freshTypeVarID unit in
        y /\ Map.insert x y sub
    Just _ -> unsafeThrow "shouldn't be in map yet"

freshenUTermImpl :: TyVarSub -> TermVarSub -> UTerm -> UTerm
freshenUTermImpl ksub sub (UTerm label kids) =
    let label' /\ ksub' /\ sub' = freshenLabel ksub sub label in
    UTerm label' (map (freshenUTermImpl ksub' sub') kids)

freshenTerm :: Term -> Term
freshenTerm t = uTermToTerm (freshenUTermImpl Map.empty Map.empty (termToUTerm t))


--data UTooth = UTooth Label (List UTerm) (List UTerm) -- The left and right children
freshenUPathImpl :: TyVarSub -> TermVarSub -> List UTooth -> TyVarSub /\ TermVarSub /\ List UTooth
freshenUPathImpl ksub sub Nil = ksub /\ sub /\ Nil
freshenUPathImpl ksub sub ((UTooth label leftKids rightKids) : up) =
    let label' /\ ksub' /\ sub' = freshenLabel ksub sub label in
    let mapper = map (freshenUTermImpl ksub' sub') in
    let innerksub /\ innersub /\ up' = freshenUPathImpl ksub' sub' up in
    innerksub /\ innersub /\ (UTooth label' (mapper leftKids) (mapper rightKids)) : up'

freshenTermPath :: List Tooth -> TyVarSub /\ TermVarSub /\ List Tooth
freshenTermPath path =
    let upath = (map toothToUTooth) path in
    let innerksub /\ innersub /\ upath' = freshenUPathImpl Map.empty Map.empty upath in
    innerksub /\ innersub /\ (map uToothToTooth upath')

freshenLabel :: TyVarSub -> TermVarSub -> Label -> Label /\ TyVarSub /\ TermVarSub
freshenLabel ksub sub (LApp md {-Term-} {-Term-} argTy outTy) =
    LApp md {--} {--} (subType ksub argTy) (subType ksub outTy)
    /\ ksub /\ sub
freshenLabel ksub sub (LLambda md (TermBind xmd x) ty1 {-Term-} ty2) =
    let x' /\ sub' = getTermVarID x sub in
    LLambda md (TermBind xmd x') (subType ksub ty1) (subType ksub ty2)
    /\ ksub /\ sub'
freshenLabel ksub sub (LVar md x tyArgs) =
    LVar md (maybe x (\x -> x) (Map.lookup x sub)) (map (subTypeArg (convertSub ksub)) tyArgs)
    /\ ksub /\ sub
freshenLabel ksub sub (LLet md (TermBind xmd x) tyBinds {-Term-} defTy {-Term-} bodyTy) =
    let x' /\ sub' = getTermVarID x sub in
    let tyVarIds = map (\(TypeBind _ tyBindId) -> tyBindId) tyBinds in
    let ksub2 = genFreshener tyVarIds in
    let tyBinds' = map (\(TypeBind tbmd id) -> TypeBind tbmd (lookup' id ksub2)) tyBinds in
    let ksub' = union' ksub ksub2 in
    LLet md (TermBind xmd x') tyBinds' {--} (subType ksub defTy) {--} (subType ksub bodyTy)
    /\ ksub' /\ sub'
freshenLabel ksub sub (LData md (TypeBind xmd x) tyBinds ctrs {-Term-} bodyTy) =
    let x' /\ ksub' = getTypeVarID x ksub in
    -- freshen the typebinds
    let tyVarIds = map (\(TypeBind _ tyBindId) -> tyBindId) tyBinds in
    let ksub2 = genFreshener tyVarIds in
    let tyBinds' = map (\(TypeBind tbmd id) -> TypeBind tbmd (lookup' id ksub2)) tyBinds in
    let ksub'' = union' ksub' ksub2 in
    -- freshen the constructor names
    let ctrVars = map (\(Constructor _ (TermBind _ xCtr) _) -> xCtr) ctrs in
    let sub2 = genTermFreshener ctrVars in
    let ctrs' = map (\(Constructor cmd (TermBind xCtrMd xCtr) ctrParams) -> Constructor cmd (TermBind xCtrMd (lookup' xCtr sub2)) ctrParams) ctrs in
    let sub' = union' sub sub2 in
    LData md (TypeBind xmd x') tyBinds' ctrs' (subType ksub'' bodyTy)
    /\ ksub'' /\ sub'
freshenLabel ksub sub (LTLet md tyBind tyBinds def {-Term-} bodyTy) = hole' "freshenLabel"
freshenLabel ksub sub (LTypeBoundary md ch1 {-Term-}) =
    LTypeBoundary md (renChange ksub ch1) /\ ksub /\ sub
freshenLabel ksub sub (LContextBoundary md x vc {-Term-}) =
    LContextBoundary md (maybe x (\x -> x) (Map.lookup x sub)) (subVarChange (convertSub ksub) vc)
    /\ ksub /\ sub
freshenLabel ksub sub (LHole md) = LHole md /\ ksub /\ sub
freshenLabel ksub sub (LBuffer md {-Term-} bufTy {-Term-} bodyTy) =
    LBuffer md {--} (subType ksub bufTy) {--} (subType ksub bodyTy)
    /\ ksub /\ sub
