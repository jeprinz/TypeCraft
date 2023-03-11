module TypeCraft.Purescript.Unification where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Alpha
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD

import Control.Monad.Except as Except
import Control.Monad.State as State
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import Data.List ((:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Debug as Debug
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (normalizeType)
import TypeCraft.Purescript.Util (hole')

-- * unification
type Unify a
  -- = StateT Sub (Except String) a
  = Except.ExceptT String (State.State Sub) a


runUnify :: forall a. Unify a -> Either String (a /\ Sub)
-- runUnify m = either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
runUnify m = case State.runState (Except.runExceptT m) emptySub of
  Left msg /\ _ -> Left msg
  Right a /\ sub -> Right (a /\ sub)

normThenUnify :: TypeAliasContext -> Type -> Type -> Unify Type
normThenUnify actx ty1 ty2 = unify (normalizeType actx ty1) (normalizeType actx ty2)

-- NOTE: output substitution substitutes holes in ty2 for things in ty1
-- either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
-- when it unifies two holes, it subs the one on the left for the one on the right (Note that this specification matters, and if unify is ever rewritten it needs to respect this spec).
unify :: Type -> Type -> Unify Type
unify ty1 ty2 = case ty1 /\ ty2 of
  THole _ hid1 _ _ /\ THole _ hid2 _ _ | hid1 == hid2 -> pure ty1 -- need this case, otherwise unifying a hole with itself would fail occurs check!
  THole _ hid w _ /\ _ -> do
    Debug.traceM "[!] don't forget to do this"
    -- TODO: checkOccursTypeVarAny w ty2 -- Need to check that nothing in w appears in ty2
    checkOccurs hid ty2
    State.modify_ (\sub -> sub { subTHoles = Map.insert hid ty2 sub.subTHoles })
    pure ty2
  _ /\ THole _ hid _ _ -> unify ty2 ty1
  Arrow md tyA1 tyB1 /\ Arrow _ tyA2 tyB2 -> Arrow md <$> unify tyA1 tyA2 <*> unify tyB1 tyB2
  -- TODO: handle type arguments
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
    THole _ hid' _ _ -> when (hid == hid') <<< Except.throwError $ "occurence check fail; the type hole id '" <> show hid <> "' appears in the type '" <> show ty <> "'"
    TNeu _ _ args -> traverse_ (go <<< \(TypeArg _ ty) -> ty) args

checkOccursAny :: Set.Set TypeHoleID -> Type -> Unify Unit
checkOccursAny hids ty = go ty
  where
  go = case _ of
    Arrow _ ty1 ty2 -> do
      checkOccursAny hids ty1
      checkOccursAny hids ty2
    THole _ hid _ _ -> when (Set.member hid hids) <<< Except.throwError $ "occurence ANY check fail; the type hole id '" <> show hid <> "' appears in the type '" <> show ty <> "'"
    TNeu _ _ args -> traverse_ (go <<< \(TypeArg _ ty) -> ty) args

checkOccursTypeVarAny :: Set.Set TypeVarID -> Type -> Unify Unit
checkOccursTypeVarAny _ _ = unsafeThrow "TODO: impl checkOccursTypeVarAny"

-- create neutral form from variable of first type that can fill the hole of the
-- second type
fillNeutral :: TypeAliasContext -> PolyType -> TermVarID -> Type -> Unify Term
fillNeutral actx pty id ty = fillNeutralImpl actx pty id ty emptySub List.Nil

fillNeutralImpl :: TypeAliasContext -> PolyType -> TermVarID -> Type -> Sub -> List.List TypeArg -> Unify Term
fillNeutralImpl actx pty id ty sub tyArgs = case pty of
  Forall x pty' ->
    let h = (freshTHole unit) in
    fillNeutralImpl actx pty' id ty sub{subTypeVars= Map.insert x h sub.subTypeVars} ((TypeArg defaultTypeArgMD h) List.: tyArgs)
  PType ty' -> fillNeutral' actx (applySubType sub ty') id ty tyArgs

{-
NOTE: when creating a variable to place into a new neutral form, if the type is a hole, you can prioritize as many or as few
arguments. fillNeutral'' prioritizes many arguments, and fillNeutral' prioritizes few.
-}
--fillNeutral'' :: TypeAliasContext -> Type -> TermVarID -> Type -> List.List TypeArg -> Unify Term
--fillNeutral'' actx ty id ty' tyArgs = case ty of
--  Arrow _ ty1 ty2 ->
--    (\tm -> App defaultAppMD tm (freshHole unit) ty1 ty2)
--      <$> fillNeutral'' actx ty2 id ty' tyArgs
--  _ -> do
--    void $ normThenUnify actx ty' ty
--    pure $ Var defaultVarMD id tyArgs

-- first type is that of variable, second type is that of location that variable will fill
fillNeutral' :: TypeAliasContext -> Type -> TermVarID -> Type -> List.List TypeArg -> Unify Term
fillNeutral' actx ty id ty' tyArgs =
--    \trace ("getting called with: " <> show ty') \_ ->
    case runUnify (normThenUnify actx ty' ty) of
    Left msg ->
        case ty of
        Arrow _ ty1 ty2 -> do
            tm <- fillNeutral' actx ty2 id ty' tyArgs
            pure $ App defaultAppMD tm (freshHole unit) ty1 ty2
        _ -> Except.throwError msg
    Right (_ /\ sub) -> do
        State.modify_ (\_ -> sub)
        pure $ Var defaultVarMD id tyArgs -- TODO: this is where we need to not just have Nil but actually use the type parameters. Probably have the Var get passed as argument from fillNeutral.
--runUnify :: forall a. Unify a -> Either String (a /\ Sub)