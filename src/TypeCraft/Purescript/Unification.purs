module TypeCraft.Purescript.Unification where

import Prelude
import Data.Tuple.Nested (type (/\), (/\))
import Prim hiding (Type)
import Control.Monad.Except as Except
import Control.Monad.State as State
import Data.Map as Map
import TypeCraft.Purescript.Grammar
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.List as List
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (hole')

-- * unification
type Unify a
  -- = StateT Sub (Except String) a
  = Except.ExceptT String (State.State Sub) a

type Sub
  = { subTypeVars :: Map.Map TypeVarID Type
    , subTHoles :: Map.Map TypeHoleID Type
    }

applySubType :: Sub -> Type -> Type
applySubType sub = case _ of
  Arrow md ty1 ty2 -> Arrow md (applySubType sub ty1) (applySubType sub ty2)
  -- Note from Jacob: this former version of the line was causing an infinite loop
--  ty@(THole md hid) -> applySubType sub $ maybe ty identity (Map.lookup hid sub.subTHoles)
  ty@(THole md hid) -> maybe ty identity (Map.lookup hid sub.subTHoles)
  -- Question from Jacob: Why is there a special case for Nil?
  ty@(TNeu md id List.Nil) -> applySubType sub $ maybe ty identity (Map.lookup id sub.subTypeVars)
  TNeu md id args -> TNeu md id ((\(TypeArg md ty) -> TypeArg md (applySubType sub ty)) <$> args)

applySubChange :: Sub -> Change -> Change
applySubChange sub = case _ of
  CArrow ty1 ty2 -> CArrow (applySubChange sub ty1) (applySubChange sub ty2)
  ty@(CHole hid) -> maybe ty tyInject (Map.lookup hid sub.subTHoles)
  -- Question from Jacob: Why is there a special case for Nil?
  ty@(CNeu id List.Nil) -> applySubChange sub $ maybe ty tyInject (Map.lookup id sub.subTypeVars)
  CNeu id args -> CNeu id (applySubChangeParam sub <$> args)
  Replace ty1 ty2 -> Replace (applySubType sub ty1) (applySubType sub ty2)
  Plus ty ch -> Plus (applySubType sub ty) (applySubChange sub ch)
  Minus ty ch -> Minus (applySubType sub ty) (applySubChange sub ch)
--data ChangeParam
--  = ChangeParam Change
--  | PlusParam Type
--  | MinusParam Type
applySubChangeParam :: Sub -> ChangeParam -> ChangeParam
applySubChangeParam sub = case _ of
    ChangeParam ch -> ChangeParam (applySubChange sub ch)
    PlusParam ty -> PlusParam (applySubType sub ty)
    MinusParam ty -> MinusParam (applySubType sub ty)

emptySub :: Sub
emptySub = { subTypeVars: Map.empty, subTHoles: Map.empty }

runUnify :: forall a. Unify a -> Either String (a /\ Sub)
-- runUnify m = either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
runUnify m = case State.runState (Except.runExceptT m) emptySub of
  Left msg /\ _ -> Left msg
  Right a /\ sub -> Right (a /\ sub)

-- either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
unify :: Type -> Type -> Unify Type
unify ty1 ty2 = case ty1 /\ ty2 of
  THole _ hid /\ _ -> do
    checkOccurs hid ty2
    State.modify_ (\sub -> sub { subTHoles = Map.insert hid ty2 sub.subTHoles })
    pure ty2
  _ /\ THole _ hid -> do
    checkOccurs hid ty1
    State.modify_ (\sub -> sub { subTHoles = Map.insert hid ty2 sub.subTHoles })
    pure ty2
  Arrow md tyA1 tyB1 /\ Arrow _ tyA2 tyB2 -> Arrow md <$> unify tyA1 tyA2 <*> unify tyB1 tyB2
  _
    | ty1 == ty2 -> pure ty1
    | otherwise -> Except.throwError $ "types do not unify: (" <> show ty1 <> ") ~ (" <> show ty2 <> ")"

-- throws error if the type hole id appears in the type
checkOccurs :: TypeHoleID -> Type -> Unify Unit
checkOccurs hid ty = go ty
  where
  go = case _ of
    Arrow _ ty1 ty2 -> do
      checkOccurs hid ty1
      checkOccurs hid ty2
    THole _ hid' -> when (hid == hid') <<< Except.throwError $ "occurence check fail; the type hole id '" <> show hid <> "' appears in the type '" <> show ty <> "'"
    TNeu _ _ args -> traverse_ (go <<< \(TypeArg _ ty) -> ty) args

-- create neutral form from variable of first type that can fill the hole of the
-- second type
fillNeutral :: PolyType -> TermVarID -> Type -> Unify Term
fillNeutral pty id ty = case pty of
  Forall _ pty' -> fillNeutral pty' id ty
  PType ty' -> fillNeutral' ty' id ty

fillNeutral' :: Type -> TermVarID -> Type -> Unify Term
fillNeutral' ty id ty' = case ty of
  Arrow _ ty1 ty2 ->
    (\tm -> App defaultAppMD tm (freshHole unit) ty1 ty2)
      <$> fillNeutral' ty2 id ty'
  _ -> do
    void $ unify ty ty'
    pure $ Var defaultVarMD id List.Nil


subTerm :: Sub -> Term -> Term
subTerm sub =
    let rec = subTerm sub in
    let st = applySubType sub in
    case _ of
    App md t1 t2 argTy outTy -> App md (rec t1) (rec t2) (st argTy) (st outTy)
    Lambda md tBind argTy body bodyTy -> Lambda md tBind (st argTy) (rec body) (st bodyTy)
    Var md x tyArgs -> Var md x (map (\(TypeArg md ty) -> TypeArg md (st ty)) tyArgs)
    Let md tBind tyBinds def defTy body bodyTy -> Let md tBind tyBinds (rec def) (st defTy) (rec body) (st bodyTy)
    Data md tyBind tyBinds ctrs body bodyTy -> hole' "subTerm" -- Need to define subConstructor
    TLet md tyBind tyBinds def body bodyTy -> TLet md tyBind tyBinds (st def) (rec body) (st bodyTy)
    TypeBoundary md ch body -> TypeBoundary md (applySubChange sub ch) (rec body)
    ContextBoundary md x ch body -> hole' "subTerm" -- ContextBoundary md x (applySubChange sub ch) (rec body)
    Hole md -> Hole md
    Buffer md def defTy body bodyTy -> Buffer md (rec def) (st defTy) (rec body) (st bodyTy)

--data PolyChange
--  = CForall TypeVarID PolyChange
--  | PPlus TypeVarID PolyChange
--  | PMinus TypeVarID PolyChange
--  | PChange Change
--
--data VarChange
--  = VarTypeChange PolyChange
--  | VarDelete PolyType
--  | VarInsert PolyType

-- WIll also need: subTermPath
-- Shouldn't need it for any other kind of path, since unifications can only be triggered when filling a term.