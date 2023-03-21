module TypeCraft.Purescript.FreshenClipboard where

import Prelude

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar

import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.MD (defaultTNeuMD)
import TypeCraft.Purescript.Util (lookup', mapKeys, union')
import TypeCraft.Purescript.Alpha
import TypeCraft.Purescript.Freshen (TyVarSub)

type TermVarSub = Map TermVarID TermVarID

getTermVarID :: TermVarID -> TermVarSub -> TermVarID /\ TermVarSub
getTermVarID x sub = case Map.lookup x sub of
    Nothing -> let y = freshTermVarID unit in
        y /\ Map.insert x y sub
    Just y -> y /\ sub

freshenTerm :: TyVarSub -> TermVarSub -> Term -> Term
freshenTerm ksub sub term =
    let ksub2 =  { subTypeVars : (map (\x -> TNeu defaultTNeuMD (TypeVar x) List.Nil) ksub) , subTHoles : Map.empty} in
    let rec = freshenTerm ksub sub in -- TODO: get rid of this, because it could lead to bugs where I don't use updated sub?
    let st = applySubType ksub2 in
    case term of
    App md t1 t2 argTy outTy -> App md (rec t1) (rec t2) (st argTy) (st outTy)
    Lambda md (TermBind xmd x) argTy body bodyTy ->
        let x' /\ sub' = getTermVarID x sub in
        Lambda md (TermBind xmd x') (st argTy) (freshenTerm ksub sub' body) (st bodyTy)
    Var md x tyArgs -> Var md x (map (\(TypeArg md' ty) -> TypeArg md' (st ty)) tyArgs)
    -- TODO this case:
    Let md tBind tyBinds def defTy body bodyTy -> Let md tBind tyBinds (rec def) (st defTy) (rec body) (st bodyTy)
    -- TODO this case:
    Data md tyBind tyBinds ctrs body bodyTy -> Data md tyBind tyBinds (map (subConstructor ksub2) ctrs) (rec body) (st bodyTy)
    -- TODO this case:
    TLet md tyBind tyBinds def body bodyTy -> TLet md tyBind tyBinds (st def) (rec body) (st bodyTy)
    TypeBoundary md ch body -> TypeBoundary md (applySubChange ksub2 ch) (rec body)
    ContextBoundary md x ch body -> ContextBoundary md x (subVarChange ksub2 ch) (rec body)
    Hole md -> Hole md
    Buffer md def defTy body bodyTy -> Buffer md (rec def) (st defTy) (rec body) (st bodyTy)
