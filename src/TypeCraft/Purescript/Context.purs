module TypeCraft.Purescript.Context where

import Prelude
import Data.Tuple.Nested (type (/\), (/\))
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.Map.Internal (Map, insert, empty, lookup, delete, filterKeys)
import Data.Set (member)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Freshen (freshenChange)
import Effect.Exception.Unsafe (unsafeThrow)
import Data.List (List(..), (:))
import TypeCraft.Purescript.MD (defaultArrowMD)
import Data.Set (Set)
import Data.Set as Set
import TypeCraft.Purescript.Kinds (bindsToKind)
import Data.Map.Internal (empty, lookup, insert, union)
import TypeCraft.Purescript.MD (TypeBindMD)
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Freshen

{-
This file defines term contexts and type contexts!
-}
--------------------------------------------------------------------------------
-------------- Regular contexts -----------------------------------------------
--------------------------------------------------------------------------------
type TermContext = Map TermVarID PolyType
type TypeContext = Map TypeVarID Kind

--------------------------------------------------------------------------------
-------------- Change contexts ------------------------------------------------
--------------------------------------------------------------------------------

data VarChange = VarTypeChange PolyChange | VarDelete -- | VarInsert PolyType
-- Let-bound on left and lambda-bound variables on right
-- TODO: TODO: TODO: I need to combine these and instead have Map TermVarID (K)
type ChangeCtx = Map TermVarID VarChange

data TVarChange = TVarKindChange KindChange | TVarDelete | TVarTypeChange Change
type KindChangeCtx = Map TypeVarID TVarChange
ctxKindCons :: KindChangeCtx -> TypeBind -> TVarChange -> KindChangeCtx
ctxKindCons kctx (TypeBind _ x) c = insert x c kctx

type CAllContext = KindChangeCtx /\ ChangeCtx

addLetToCCtx :: ChangeCtx -> TermBind -> List TypeBind -> Type -> ChangeCtx
addLetToCCtx ctx tBind@(TermBind _ x) tyBinds ty =
        insert x (VarTypeChange (pTyInject (tyBindsWrapType tyBinds ty))) ctx

removeLetFromCCtx :: CAllContext -> TermBind -> CAllContext
removeLetFromCCtx (kctx /\ ctx) (TermBind _ x) = kctx /\ delete x ctx

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

-- term metadata that is per-term, as opposed to MDContext which is more accumulative
type MDType = { -- needs to be in MDContext, because it needs to be in the state: if I have select the left of an app, then the term inside needs to know that when its rendered
    onLeftOfApp :: Boolean
    , onRightOfApp :: Boolean
    , onLeftOfArrow :: Boolean
    , indented :: Boolean
}

defaultMDType :: MDType
defaultMDType = {
    onLeftOfApp : false
    , onRightOfApp : false
    , onLeftOfArrow : false
    , indented : false
    }

--------------------------------------------------------------------------------
-------------- Complete Context -----------------------------------------------
--------------------------------------------------------------------------------

type AllContext = {
    mdkctx :: MDTypeContext
    , mdctx :: MDTermContext
    , kctx :: TypeContext
    , ctx :: TermContext
}

-- TODO: when I properly deal with parameters to types, this will have to be modified!
tyBindsWrapType :: List TypeBind -> Type -> PolyType
tyBindsWrapType Nil ty = PType ty
tyBindsWrapType (tyBind : tyBinds) ty = Forall tyBind (tyBindsWrapType tyBinds ty)

constructorTypes :: TypeBind -> List TypeBind -> List Constructor -> Map TermVarID PolyType
constructorTypes dataType tyBinds ctrs =
    let sub = genFreshener (map (\(TypeBind _ x) -> x) tyBinds) in
    let freshTyBinds = map (subTypeBind sub) tyBinds in
    let freshCtrs = map (subConstructor sub) ctrs in
    constructorTypesImpl dataType freshTyBinds freshCtrs

constructorTypesImpl :: TypeBind -> List TypeBind -> List Constructor -> Map TermVarID PolyType
constructorTypesImpl dataType tyBinds Nil = empty
constructorTypesImpl dataType tyBinds (Constructor _ (TermBind _ x) params : ctrs)
    = insert x (ctrParamsToType hole tyBinds params) (constructorTypesImpl dataType tyBinds ctrs)

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

