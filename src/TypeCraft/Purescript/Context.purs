module TypeCraft.Purescript.Context where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Freshen
import TypeCraft.Purescript.Grammar

import Data.List (List(..), (:))
import Data.Map.Internal (Map, delete, empty, filterKeys, insert, lookup)
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
import TypeCraft.Purescript.MD (TypeBindMD)
import TypeCraft.Purescript.MD (defaultArrowMD)
import TypeCraft.Purescript.Util (hole')

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

data TypeAliasChange
  = TAForall TypeVarID TypeAliasChange
  | TAPlus TypeVarID TypeAliasChange
  | TAMinus TypeVarID TypeAliasChange
  | TAChange Change

data TVarChange = TVarKindChange KindChange (Maybe TypeAliasChange) | TVarDelete -- Do I need TVarInsert? Does TVarDelete need more parameters?
type KindChangeCtx = Map TypeVarID TVarChange
ctxKindCons :: KindChangeCtx -> TypeBind -> TVarChange -> KindChangeCtx
ctxKindCons kctx (TypeBind _ x) c = insert x c kctx

type CAllContext = KindChangeCtx /\ ChangeCtx

addLetToCCtx :: ChangeCtx -> TermBind -> List TypeBind -> Type -> ChangeCtx
addLetToCCtx ctx tBind@(TermBind _ x) tyBinds ty =
        insert x (VarTypeChange (pTyInject (tyBindsWrapType tyBinds ty))) ctx

removeLetFromCCtx :: CAllContext -> TermBind -> CAllContext
removeLetFromCCtx (kctx /\ ctx) (TermBind _ x) = kctx /\ delete x ctx

kCtxInject :: TypeContext -> TypeAliasContext -> KindChangeCtx
kCtxInject kctx actx = mapMaybeWithKey (\x kind
        -> Just $ TVarKindChange (kindInject kind)
            (case lookup x actx of
                Nothing -> Nothing
                Just (tyBinds /\ def) ->
                    let bindsToTAC :: List TypeBind -> TypeAliasChange
                        bindsToTAC Nil = TAChange (tyInject def)
                        bindsToTAC ((TypeBind _ x) : tyBinds) = TAForall x (bindsToTAC tyBinds)
                    in Just (bindsToTAC tyBinds))
    ) kctx

ctxInject :: TermContext -> ChangeCtx
ctxInject ctx = map (\ty -> VarTypeChange (pTyInject ty)) ctx

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

constructorTypes :: TypeBind -> List TypeBind -> List Constructor -> Map TermVarID PolyType
constructorTypes dataType tyBinds ctrs =
    let sub = genFreshener (map (\(TypeBind _ x) -> x) tyBinds) in
    let freshTyBinds = map (subTypeBind sub) tyBinds in
    let freshCtrs = map (subConstructor sub) ctrs in
    constructorTypesImpl dataType freshTyBinds freshCtrs

constructorTypesImpl :: TypeBind -> List TypeBind -> List Constructor -> Map TermVarID PolyType
constructorTypesImpl dataType tyBinds Nil = empty
constructorTypesImpl dataType tyBinds (Constructor _ (TermBind _ x) params : ctrs)
    = insert x (ctrParamsToType (hole' "constructorTypesImpl") tyBinds params) (constructorTypesImpl dataType tyBinds ctrs)

constructorNames :: List Constructor -> Map TermVarID String
constructorNames Nil = empty
constructorNames (Constructor _ (TermBind xmd x) params : ctrs)
    = insert x xmd.varName (constructorNames ctrs)

ctrParamsToType :: Type -> List TypeBind -> List CtrParam -> PolyType
ctrParamsToType dataType tyBinds ctrParams = tyBindsWrapType tyBinds (ctrParamsToTypeImpl dataType ctrParams)
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
removeDataFromCtx ctxs tyBind@(TypeBind xmd x) tyBinds ctrs =
    let ctrIds = constructorIds ctrs in
    ctxs{
        kctx = delete x ctxs.kctx
        , mdkctx = delete x ctxs.mdkctx
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
removeTLetFromCtx ctxs (TypeBind _ x) = ctxs{kctx= delete x ctxs.kctx, mdkctx= delete x ctxs.mdkctx, actx = delete x ctxs.actx}

addLetToCtx :: AllContext -> TermBind -> List TypeBind -> Type -> AllContext
addLetToCtx ctxs tBind@(TermBind xmd x) tyBinds defTy
    = ctxs{ctx = insert x (tyBindsWrapType tyBinds defTy) ctxs.ctx, mdctx = insert x xmd.varName ctxs.mdctx}


-- TODO: some of these things need to be organized into different files:
tyBindsWrapKind :: List TypeBind -> Kind -> Kind
tyBindsWrapKind Nil k = k
tyBindsWrapKind (_ : tyBinds) k = KArrow (tyBindsWrapKind tyBinds k)

