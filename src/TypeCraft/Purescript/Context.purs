module TypeCraft.Purescript.Context where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.Map.Internal (Map, insert, empty, lookup)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Freshen (freshenChange)
import Effect.Exception.Unsafe (unsafeThrow)
import Data.List (List(..), (:))
import TypeCraft.Purescript.MD (defaultArrowMD)

{-
This file defines term contexts and type contexts!
-}
--------------------------------------------------------------------------------
-------------- Regular contexts -----------------------------------------------
--------------------------------------------------------------------------------
type TermContext = Map TermVarID Type
type TypeContext = Map TypeVarID Kind

--------------------------------------------------------------------------------
-------------- Change contexts ------------------------------------------------
--------------------------------------------------------------------------------

data VarChange = VarTypeChange Change | VarDelete -- | VarInsert Type
-- Let-bound on left and lambda-bound variables on right
-- TODO: TODO: TODO: I need to combine these and instead have Map TermVarID (K)
data ChangeCtx = ChangeCtx (Map TermVarID VarChange) (Map TermVarID VarChange)
ctxLetCons :: ChangeCtx -> TermBind -> VarChange -> ChangeCtx
ctxLetCons (ChangeCtx lets lams) (TermBind _ x) c = ChangeCtx (insert x c lets) lams

ctxLambdaCons :: ChangeCtx -> TermBind -> VarChange -> ChangeCtx
ctxLambdaCons (ChangeCtx lets lams) (TermBind _ x) c = ChangeCtx lets (insert x c lams)

data TVarChange = TVarKindChange KindChange | TVarDelete | TVarTypeChange Change
type KindChangeCtx = Map TypeVarID TVarChange
ctxKindCons :: KindChangeCtx -> TypeBind -> TVarChange -> KindChangeCtx
ctxKindCons kctx (TypeBind _ x) c = insert x c kctx

ctxLookup :: TermVarID -> ChangeCtx -> VarChange
ctxLookup x (ChangeCtx letCtx lamCtx) = case lookup x lamCtx of
                                      Just c -> c
                                      Nothing -> case lookup x letCtx of
                                                 Just (VarTypeChange c) -> VarTypeChange (freshenChange c)
                                                 Just VarDelete -> VarDelete
                                                 Nothing -> unsafeThrow "shouldn't get ehre"

--data Contexts = Contexts TermContext ChangeCtx

-- TODO: when I properly deal with parameters to types, this will have to be modified!
constructorTypes :: Type -> List Constructor -> Map TermVarID Type
constructorTypes dataType Nil = empty
constructorTypes dataType (Constructor _ (TermBind _ x) params : ctrs)
    = insert x (ctrParamsToType dataType params) (constructorTypes dataType ctrs)

ctrParamsToType :: Type -> List CtrParam -> Type
ctrParamsToType dataType Nil = dataType
ctrParamsToType dataType (CtrParam _ ty : params) = Arrow defaultArrowMD ty (ctrParamsToType dataType params)

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
}

defaultMDType :: MDType
defaultMDType = {onLeftOfApp : false, onRightOfApp : false}

--------------------------------------------------------------------------------
-------------- Complete Context -----------------------------------------------
--------------------------------------------------------------------------------

type AllContext = {
    kctx :: TypeContext
    , ctx :: TermContext
    , mdctx :: MDContext
}
