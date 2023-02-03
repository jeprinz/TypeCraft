module TypeCraft.Purescript.Context where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Freshen
import TypeCraft.Purescript.Grammar

import Data.List (List(..), (:))
import Data.Map.Internal (Map, empty, filterKeys, insert, lookup)
import Data.Map.Internal (empty, lookup, insert, union, mapMaybeWithKey)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set (member)
import Data.Set as Set
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Util (hole', hole, delete')
import TypeCraft.Purescript.Util (lookup')

{-
This file defines term contexts and type contexts!
-}
--------------------------------------------------------------------------------
-------------- Regular contexts -----------------------------------------------
--------------------------------------------------------------------------------
type TermContext = Map TermVarID PolyType
type TypeContext = Map TypeVarID Kind
type TypeAliasContext = Map TypeVarID (List TypeBind /\ Type) -- The array is the free variables in the Type.

--------------------------------------------------------------------------------
-------------- Change contexts ------------------------------------------------
--------------------------------------------------------------------------------

-- Let-bound on left and lambda-bound variables on right
-- TODO: TODO: TODO: I need to combine these and instead have Map TermVarID (K)
type ChangeCtx = Map TermVarID VarChange

ctxKindCons :: KindChangeCtx -> TypeBind -> TVarChange -> KindChangeCtx
ctxKindCons kctx (TypeBind _ x) c = insert x c kctx

type CAllContext = KindChangeCtx /\ ChangeCtx

addLetToCCtx :: ChangeCtx -> TermBind -> List TypeBind -> Type -> ChangeCtx
addLetToCCtx ctx tBind@(TermBind _ x) tyBinds ty =
        insert x (VarTypeChange (pTyInject (tyBindsWrapType tyBinds ty))) ctx

addLetToKCCtx :: KindChangeCtx -> List TypeBind -> KindChangeCtx
addLetToKCCtx kctx Nil = kctx
addLetToKCCtx kctx (TypeBind _ x : tyBinds) = addLetToKCCtx (insert x (TVarKindChange KCType Nothing) kctx) tyBinds

removeLetFromKCCtx :: KindChangeCtx -> List TypeBind -> KindChangeCtx
removeLetFromKCCtx kctx Nil = kctx
removeLetFromKCCtx kctx (TypeBind _ x : tyBinds) = removeLetFromKCCtx (delete' x kctx) tyBinds

removeLetFromCCtx :: CAllContext -> TermBind -> CAllContext
removeLetFromCCtx (kctx /\ ctx) (TermBind _ x) = kctx /\ delete' x ctx

kCtxInject :: TypeContext -> TypeAliasContext -> KindChangeCtx
kCtxInject kctx actx = mapMaybeWithKey (\x kind
        -> Just $ TVarKindChange (kindInject kind)
            (case lookup x actx of
                Nothing -> Nothing
                Just (tyBinds /\ def) ->
                    let bindsToTAC :: List TypeBind -> TypeAliasChange
                        bindsToTAC Nil = TAChange (tyInject def)
                        bindsToTAC (tyBind : tyBinds) = TAForall tyBind (bindsToTAC tyBinds)
                    in Just (bindsToTAC tyBinds))
    ) kctx

ctxInject :: TermContext -> ChangeCtx
ctxInject ctx = map (\ty -> VarTypeChange (pTyInject ty)) ctx

--data ListCtrChange = ListCtrChangeNil | ListCtrChangeCons TermVarID ListCtrParamChange ListCtrChange
--    | ListCtrChangePlus Constructor ListCtrChange
--    | ListCtrChangeMinus Constructor ListCtrChange

-- TODO: when I properly deal with parameters to types, this will have to be modified!
tyBindsWrapChange :: List TypeBind -> Change -> PolyChange
tyBindsWrapChange Nil ch = PChange ch
tyBindsWrapChange ((TypeBind _ x) : tyBinds) ch = CForall x (tyBindsWrapChange tyBinds ch)

tyVarIdsWrapChange :: List TypeVarID -> Change -> PolyChange
tyVarIdsWrapChange Nil ch = PChange ch
tyVarIdsWrapChange (x : tyBinds) ch = CForall x (tyVarIdsWrapChange tyBinds ch)

data NameChange = NameChangeInsert String | NameChangeDelete String | NameChangeSame String
type MDTypeChangeCtx = Map TypeVarID NameChange
type MDTermChangeCtx = Map TypeVarID NameChange

mdctxInject :: MDTermContext -> MDTermChangeCtx
mdctxInject m = map NameChangeSame m

mdkctxInject :: MDTypeContext -> MDTypeChangeCtx
mdkctxInject m = map NameChangeSame m

type AllChangeContexts = ChangeCtx /\ KindChangeCtx /\ MDTermChangeCtx /\ MDTypeChangeCtx

--------------------------------------------------------------------------------
-------------- Metadatta contexts ---------------------------------------------
--------------------------------------------------------------------------------

type MDTypeContext = Map TypeVarID String
type MDTermContext = Map TermVarID String

type MDContext = {
    indentation :: Int, -- TODO: hopefully the frontend can handle this instead
    termVarNames :: MDTermContext,
    typeVarNames :: MDTypeContext
}

--------------------------------------------------------------------------------
-------------- Complete Context -----------------------------------------------
--------------------------------------------------------------------------------

type AllContext = {
    mdkctx :: MDTypeContext
    , mdctx :: MDTermContext
    , kctx :: TypeContext
    , actx :: TypeAliasContext -- a stands for alias
    , ctx :: TermContext
}

emptyAllContext :: AllContext
emptyAllContext = {
    mdkctx: empty,
    mdctx: empty,
    kctx: empty,
    actx: empty,
    ctx: empty
}

-- TODO: when I properly deal with parameters to types, this will have to be modified!
tyBindsWrapType :: List TypeBind -> Type -> PolyType
tyBindsWrapType Nil ty = PType ty
tyBindsWrapType ((TypeBind _ x) : tyBinds) ty = Forall x (tyBindsWrapType tyBinds ty)

tyVarIdsWrapType :: List TypeVarID -> Type -> PolyType
tyVarIdsWrapType Nil ty = PType ty
tyVarIdsWrapType (x : xs) ty = Forall x (tyVarIdsWrapType xs ty)

listTypeBindChWrapPolyChange :: ListTypeBindChange -> Change -> PolyChange
listTypeBindChWrapPolyChange (ListTypeBindChangeCons tyBind@(TypeBind _ x) ch) pch = CForall x (listTypeBindChWrapPolyChange ch pch)
listTypeBindChWrapPolyChange (ListTypeBindChangePlus tyBind@(TypeBind _ x) ch) pch = PPlus x (listTypeBindChWrapPolyChange ch pch)
listTypeBindChWrapPolyChange (ListTypeBindChangeMinus tyBind@(TypeBind _ x) ch) pch = PMinus x (listTypeBindChWrapPolyChange ch pch)
listTypeBindChWrapPolyChange ListTypeBindChangeNil pch = PChange pch

addTyBindChsToKCCtx :: ListTypeBindChange -> KindChangeCtx -> KindChangeCtx
addTyBindChsToKCCtx (ListTypeBindChangeCons (TypeBind _ x) ch) kctx =
    addTyBindChsToKCCtx ch (insert x (TVarKindChange KCType Nothing) kctx)
addTyBindChsToKCCtx (ListTypeBindChangePlus (TypeBind _ x) ch) kctx =
    addTyBindChsToKCCtx ch (insert x (TVarInsert Type Nothing) kctx)
addTyBindChsToKCCtx (ListTypeBindChangeMinus (TypeBind _ x) ch) kctx =
    addTyBindChsToKCCtx ch (insert x (TVarDelete Type Nothing) kctx)
addTyBindChsToKCCtx ListTypeBindChangeNil kctx = kctx

-- This probably won't be needed?
--removeTyBindChsFromKCCtx :: ListTypeBindChange -> KindChangeCtx -> KindChangeCtx
--removeTyBindChsFromKCCtx (ListTypeBindChangeCons (TypeBind _ x) ch) kctx =
--    removeTyBindChsFromKCCtx ch (delete' x kctx)
--removeTyBindChsFromKCCtx (ListTypeBindChangePlus (TypeBind _ x) ch) kctx =
--    removeTyBindChsFromKCCtx ch (delete' x kctx)
--removeTyBindChsFromKCCtx (ListTypeBindChangeMinus (TypeBind _ x) ch) kctx =
--    removeTyBindChsFromKCCtx ch (delete' x kctx)
--removeTyBindChsFromKCCtx ListTypeBindChangeNil kctx = kctx

constructorTypes :: TypeBind -> List TypeBind -> List Constructor -> Map TermVarID PolyType
constructorTypes (TypeBind _ dataType) tyBinds ctrs =
    let tyVarIds = map (\(TypeBind _ x) -> x) tyBinds in
    constructorTypesImpl dataType tyVarIds ctrs

constructorTypesImpl :: TypeVarID -> List TypeVarID -> List Constructor -> Map TermVarID PolyType
constructorTypesImpl dataType tyVarIds Nil = empty
constructorTypesImpl dataType tyVarIds (Constructor _ (TermBind _ x) params : ctrs)
    = let tyArgs = map (\x -> TypeArg defaultTypeArgMD (TNeu defaultTNeuMD x Nil)) tyVarIds
    in insert x (ctrParamsToType dataType tyVarIds params) (constructorTypesImpl dataType tyVarIds ctrs)

constructorNames :: List Constructor -> Map TermVarID String
constructorNames Nil = empty
constructorNames (Constructor _ (TermBind xmd x) params : ctrs)
    = insert x xmd.varName (constructorNames ctrs)

ctrParamsToType :: {-The datatype-}TypeVarID -> {-Datatype parameters-}List TypeVarID -> List CtrParam -> PolyType
ctrParamsToType dataType tyVarIds ctrParams =
    let sub = genFreshener tyVarIds in
    let freshTyVarIds = map (\id -> lookup' id sub) tyVarIds in
    let freshCtrParams = map (subCtrParam sub) ctrParams in
    let ctrOutType = TNeu defaultTNeuMD dataType (map (\x -> TypeArg defaultTypeArgMD (TNeu defaultTNeuMD x Nil)) freshTyVarIds) in
    tyVarIdsWrapType freshTyVarIds (ctrParamsToTypeImpl ctrOutType freshCtrParams)

ctrParamsToTypeImpl :: Type -> List CtrParam -> Type
ctrParamsToTypeImpl dataType Nil = dataType
ctrParamsToTypeImpl dataType (CtrParam _ ty : params) = Arrow defaultArrowMD ty (ctrParamsToTypeImpl dataType params)

constructorIds :: List Constructor -> Set TermVarID
constructorIds Nil = Set.empty
constructorIds (Constructor _ (TermBind _ x) _ : ctrs) = Set.insert x (constructorIds ctrs)

addDataToCtx :: AllContext -> TypeBind -> List TypeBind -> List Constructor -> AllContext
addDataToCtx ctxs tyBind@(TypeBind xmd x) tyBinds ctrs =
    ctxs{
        kctx = insert x (bindsToKind tyBinds) ctxs.kctx
        , mdkctx = insert x xmd.varName ctxs.mdkctx
        , ctx= union ctxs.ctx (constructorTypes tyBind tyBinds ctrs)
        , mdctx= union ctxs.mdctx (constructorNames ctrs)
    }

removeDataFromCtx :: AllContext -> TypeBind -> List TypeBind -> List Constructor -> AllContext
removeDataFromCtx ctxs (TypeBind _ x) _tyBinds ctrs =
    let ctrIds = constructorIds ctrs in
    ctxs{
        kctx = delete' x ctxs.kctx
        , mdkctx = delete' x ctxs.mdkctx
        , ctx= filterKeys (\k -> not (member k ctrIds)) ctxs.ctx
        , mdctx= filterKeys (\k -> not (member k ctrIds)) ctxs.mdctx
    }

addTLetToCtx :: AllContext -> TypeBind -> (List TypeBind) -> Type -> AllContext
addTLetToCtx ctxs tyBind@(TypeBind xmd x) tyBinds def =
    ctxs
        {kctx = insert x (bindsToKind tyBinds) ctxs.kctx
        , mdkctx = insert x xmd.varName ctxs.mdkctx
        , actx = insert x (tyBinds /\ def) ctxs.actx
        }

removeTLetFromCtx :: AllContext -> TypeBind -> AllContext
removeTLetFromCtx ctxs (TypeBind _ x) = ctxs{kctx= delete' x ctxs.kctx, mdkctx= delete' x ctxs.mdkctx, actx = delete' x ctxs.actx}

addLetToCtx :: AllContext -> TermBind -> List TypeBind -> Type -> AllContext
addLetToCtx ctxs tBind@(TermBind xmd x) tyBinds defTy
    = ctxs{ctx = insert x (tyBindsWrapType tyBinds defTy) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx}

addLetTypesToCtx :: AllContext -> List TypeBind -> AllContext
addLetTypesToCtx ctxs tyBinds
    = ctxs{mdkctx = addNames tyBinds ctxs.mdkctx, kctx = addKinds tyBinds ctxs.kctx}
    where
    addNames :: List TypeBind -> MDTypeContext -> MDTypeContext
    addNames Nil mdkctx = mdkctx
    addNames (TypeBind {varName} x : tyBinds) mdkctx = addNames tyBinds (insert x varName mdkctx)
    addKinds :: List TypeBind -> TypeContext -> TypeContext
    addKinds Nil kctx = kctx
    addKinds (TypeBind _ x : tyBinds) kctx = addKinds tyBinds (insert x Type kctx)

removeLetTypeFromCtx :: AllContext -> List TypeBind -> AllContext
removeLetTypeFromCtx ctxs tyBinds
    = ctxs{mdkctx = removeNames tyBinds ctxs.mdkctx, kctx = removeKinds tyBinds ctxs.kctx}
    where
    removeNames :: List TypeBind -> MDTypeContext -> MDTypeContext
    removeNames Nil mdkctx = mdkctx
    removeNames (TypeBind _ x : tyBinds) mdkctx = removeNames tyBinds (delete' x mdkctx)
    removeKinds :: List TypeBind -> TypeContext -> TypeContext
    removeKinds Nil kctx = kctx
    removeKinds (TypeBind _ x : tyBinds) kctx = removeKinds tyBinds (delete' x kctx)



-- TODO: some of these things need to be organized into different files:
tyBindsWrapKind :: List TypeBind -> Kind -> Kind
tyBindsWrapKind Nil k = k
tyBindsWrapKind (_ : tyBinds) k = KArrow (tyBindsWrapKind tyBinds k)

