module TypeCraft.Purescript.TypeChangeAlgebra2 where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Data.List (unzip, (:), List(..), foldl, all)
import Data.List as List
import Data.Map (Map, singleton, empty, unionWith, mapMaybe, insert, delete, mapMaybeWithKey)
import Data.Map as Map
import Data.Set as Set
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.Maybe (Maybe(..))
import Data.Traversable (sequence)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Substitution (Sub)
import TypeCraft.Purescript.Util
import Data.Maybe (maybe)
import Debug (trace)
import Data.Either (Either(..))

tyVarGetEndpoints :: CTypeVar -> TypeVar /\ TypeVar
tyVarGetEndpoints (CTypeVar x)  = TypeVar x /\ TypeVar x
tyVarGetEndpoints (CCtxBoundaryTypeVar k mtv name x) =
    CtxBoundaryTypeVar k mtv name x /\ CtxBoundaryTypeVar k mtv name x
tyVarGetEndpoints (PlusCtxBoundaryTypeVar k mtv name x) =
    TypeVar x /\ CtxBoundaryTypeVar k mtv name x
tyVarGetEndpoints (MinusCtxBoundaryTypeVar k mtv name x) =
    CtxBoundaryTypeVar k mtv name x /\ TypeVar x

getEndpoints :: Change -> Type /\ Type
getEndpoints (CArrow a b) =
    let a1 /\ a2 = getEndpoints a in
    let b1 /\ b2 = getEndpoints b in
    Arrow defaultArrowMD a1 b1 /\ Arrow defaultArrowMD a2 b2
getEndpoints (CHole x w s) =
    let s1 /\ s2 = getSubEndpoints s in
    THole defaultTHoleMD x w s1 /\ THole defaultTHoleMD x w s2
getEndpoints (CNeu x args) =
    let start = TNeu defaultTNeuMD in
    let ts1 /\ ts2 = getEndpointss args in
    let x1 /\ x2 = tyVarGetEndpoints x in
    let args1 = map (TypeArg defaultTypeArgMD) ts1 in
    let args2 = map (TypeArg defaultTypeArgMD) ts2 in
    start x1 args1 /\ start x2 args2
getEndpoints (Replace a b) = a /\ b
getEndpoints (Plus t c) =
    let c1 /\ c2 = getEndpoints c in
    c1 /\ Arrow defaultArrowMD t c2
getEndpoints (Minus t c) =
    let c1 /\ c2 = getEndpoints c in
    Arrow defaultArrowMD t c1 /\ c2

getEndpointss :: List ChangeParam -> List Type /\ List Type
getEndpointss Nil = Nil /\ Nil
getEndpointss (ChangeParam c : cs) =
    let t1s /\ t2s = getEndpointss cs in
    let t1 /\ t2 = getEndpoints c in
    (t1 : t1s) /\ (t2 : t2s)
getEndpointss (PlusParam t : cs) = let t1s /\ t2s = getEndpointss cs in t1s /\ t : t2s
getEndpointss (MinusParam t : cs) = let t1s /\ t2s = getEndpointss cs in (t : t1s) /\ t2s

pGetEndpoints :: PolyChange -> PolyType /\ PolyType
pGetEndpoints (CForall tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    Forall tBind pt1 /\ Forall tBind pt2
pGetEndpoints (PPlus tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    pt1 /\ Forall tBind pt2
pGetEndpoints (PMinus tBind pc) =
    let pt1 /\ pt2 = pGetEndpoints pc in
    Forall tBind pt1 /\ pt2
pGetEndpoints (PChange c) = let t1 /\ t2 = getEndpoints c in PType t1 /\ PType t2

kChGetEndpoints :: KindChange -> Kind /\ Kind
kChGetEndpoints kc = case kc of
    KCType -> Type /\ Type
    KCArrow kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        KArrow k1 /\ KArrow k2
    KPlus kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        k1 /\ KArrow k2
    KMinus kc ->
        let k1 /\ k2 = kChGetEndpoints kc in
        KArrow k1 /\ k2

taChGetEndpoints :: TypeAliasChange -> (List TypeBind /\ Type) /\ (List TypeBind /\ Type)
taChGetEndpoints tac = case tac of
    TAChange ch ->
        let ty1 /\ ty2 = getEndpoints ch in
        (Nil /\ ty1) /\ (Nil /\ ty2)
    TAForall x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        ((x : binds1) /\ ty1) /\ ((x : binds2) /\ ty2)
    TAPlus x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        (binds1 /\ ty1) /\ ((x : binds2) /\ ty2)
    TAMinus x tac ->
        let (binds1 /\ ty1) /\ (binds2 /\ ty2) = taChGetEndpoints tac in
        ((x : binds1) /\ ty1) /\ (binds2 /\ ty2)

getCtxEndpoints :: ChangeCtx -> TermContext /\ TermContext
getCtxEndpoints ctx =
    mapMaybe (case _ of
        VarInsert _ -> Nothing
        VarTypeChange pc -> Just (fst (pGetEndpoints pc))
        VarDelete pt -> Just pt) ctx
    /\
    mapMaybe (case _ of
        VarInsert pt -> Just pt
        VarTypeChange pc -> Just (snd (pGetEndpoints pc))
        VarDelete _ -> Nothing) ctx

getSubEndpoints :: Map TypeVarID SubChange -> Map TypeVarID Type /\ Map TypeVarID Type
getSubEndpoints ctx =
    mapMaybe (case _ of
        SubInsert _ -> Nothing
        SubTypeChange ch -> Just (fst (getEndpoints ch))
        SubDelete pt -> Just pt) ctx
    /\
    mapMaybe (case _ of
        SubInsert pt -> Just pt
        SubTypeChange ch -> Just (snd (getEndpoints ch))
        SubDelete _ -> Nothing) ctx

getKCtxTyEndpoints :: KindChangeCtx -> TypeContext /\ TypeContext
getKCtxTyEndpoints kctx =
    mapMaybe (case _ of
        TVarInsert _ _ _ -> Nothing
        TVarKindChange kch tac -> Just (fst (kChGetEndpoints kch))
        TVarDelete _ kind ta -> Just kind) kctx
    /\
    mapMaybe (case _ of
        TVarInsert _ kind ta -> Just kind
        TVarKindChange kch tac -> Just (snd (kChGetEndpoints kch))
        TVarDelete _ _ _ -> Nothing) kctx

getKCtxAliasEndpoints :: KindChangeCtx -> TypeAliasContext /\ TypeAliasContext
getKCtxAliasEndpoints kctx =
    mapMaybe (case _ of
        TVarInsert _ _ _ -> Nothing
        TVarKindChange kch tac -> fst <$> taChGetEndpoints <$> tac
        TVarDelete _ kind ta -> ta) kctx
    /\
    mapMaybe (case _ of
        TVarInsert _ kind ta -> ta
        TVarKindChange kch tac -> snd <$> taChGetEndpoints <$> tac
        TVarDelete _ _ _ -> Nothing) kctx

getMDCtxEndpoints :: MDTermChangeCtx -> MDTermContext /\ MDTermContext
getMDCtxEndpoints mdctx =
    mapMaybe (case _ of
        NameChangeInsert _ -> Nothing
        NameChangeSame name -> Just name
        NameChangeDelete name -> Just name) mdctx
    /\
    mapMaybe (case _ of
        NameChangeInsert name -> Just name
        NameChangeSame name -> Just name
        NameChangeDelete _  -> Nothing) mdctx

getMDKCtxEndpoints :: MDTypeChangeCtx -> MDTypeContext /\ MDTypeContext
getMDKCtxEndpoints mdkctx =
    mapMaybe (case _ of
        NameChangeInsert _ -> Nothing
        NameChangeSame name -> Just name
        NameChangeDelete name -> Just name) mdkctx
    /\
    mapMaybe (case _ of
        NameChangeInsert name -> Just name
        NameChangeSame name -> Just name
        NameChangeDelete _  -> Nothing) mdkctx

getAllEndpoints :: AllChangeContexts -> AllContext /\ AllContext
getAllEndpoints (ctx /\ kctx /\ mdctx /\ mdkctx) =
    let ctx1 /\ ctx2 = getCtxEndpoints ctx in
    let kctx1 /\ kctx2 = getKCtxTyEndpoints kctx in
    let actx1 /\ actx2 = getKCtxAliasEndpoints kctx in
    let mdctx1 /\ mdctx2 = getMDCtxEndpoints mdctx in
    let mdkctx1 /\ mdkctx2 = getMDKCtxEndpoints mdkctx in
    { ctx: ctx1, kctx: kctx1, actx: actx1, mdctx: mdctx1, mdkctx: mdkctx1 }
    /\
    { ctx: ctx2, kctx: kctx2, actx: actx2, mdctx: mdctx2, mdkctx: mdkctx2 }

