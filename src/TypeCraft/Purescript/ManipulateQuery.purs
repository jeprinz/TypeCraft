module TypeCraft.Purescript.ManipulateQuery where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Control.Monad.Except as Except
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Array.NonEmpty as Array
import Data.Either (Either(..), either)
import Data.Foldable (and, traverse_)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.String as String
import Data.Traversable (sequence, traverse)
import Data.Tuple (fst, snd)
import Data.UUID (UUID)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Change(..), Kind(..), PolyType(..), Term(..), TermVarID, Tooth(..), Type(..), TypeArg(..), TypeHoleID, TypeVarID, freshHole, freshTHole, freshTermBind, freshTypeHoleID)
import TypeCraft.Purescript.MD (defaultAppMD, defaultLambdaMD, defaultLetMD, defaultVarMD)
import TypeCraft.Purescript.ManipulateString (isIgnoreKey, manipulateString)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Query, State)
import TypeCraft.Purescript.Util (hole')

isNonemptyQueryString :: Query -> Boolean
isNonemptyQueryString query = not $ String.null query.string

manipulateQuery :: String -> State -> CursorMode -> Maybe Query
manipulateQuery key st cursorMode@{ query: query@{ string, completionGroup_i, completionGroupItem_i } }
  | key == "ArrowUp" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i - 1 }
  | key == "ArrowDown" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i + 1 }
  | key == "ArrowLeft" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i - 1 }
  | key == "ArrowRight" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i + 1 }
  | otherwise = do
    traceM $ "manipulateQuery.key = " <> key
    string' <- manipulateString key string
    pure
      query
        { string = string'
        , completionGroup_i = 0
        , completionGroupItem_i = 0
        , completionGroups = calculateCompletionsGroups string' st cursorMode
        }

kindaStartsWith :: String -> String -> Boolean
kindaStartsWith str pre =
  and
    [ String.length pre > 0 -- prefix can't be empty
    , isJust $ String.stripPrefix (String.Pattern (String.take (String.length str) pre)) str
    ]

calculateCompletionsGroups :: String -> State -> CursorMode -> Array (Array Completion)
calculateCompletionsGroups str st cursorMode = case cursorMode.cursorLocation of
  TermCursor ctxs ty path tm ->
    Writer.execWriter do
      {-
    use ctxs.mdctx.termVarNames to list names
    filter names by kindaStartWith
    -}
      -- var
      traverse_
        ( \(id /\ varName) -> case Map.lookup id ctxs.ctx of
            Nothing -> unsafeThrow $ "the entry '" <> show (id /\ varName) <> "' was found in the ctxs.mdctx, but not in the ctxs.ctx: '" <> show ctxs.ctx <> "'"
            Just pty ->
              when (str `kindaStartsWith` varName) do
                case runUnify (fillNeutral pty id ty) of
                  Left _msg -> pure unit
                  Right (tm' /\ sub) -> Writer.tell [ [ CompletionTerm tm' (applySubType sub ty) ] ]
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- lam
      when (str `kindaStartsWith` "lam")
        $ Writer.tell
            [ [ let
                  alpha = freshTHole unit
                in
                  CompletionTermPath -- lam (~ : alpha) ↦ ({} : ty)
                    (List.fromFoldable [ Lambda3 defaultLambdaMD (freshTermBind Nothing) alpha ty ])
                    (Plus alpha (Replace ty ty))
              ]
            ]
      -- let
      when (str `kindaStartsWith` "let")
        $ Writer.tell
            [ [ CompletionTermPath -- let ~<∅> : alpha = ? in {} : ty
                  (List.fromFoldable [ Let5 defaultLetMD (freshTermBind Nothing) List.Nil (freshHole unit) (freshTHole unit) ty ])
                  (Replace ty ty)
              ]
            ]
  _ -> [] -- TODO: impl

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
  ty@(THole md hid) -> applySubType sub $ maybe ty identity (Map.lookup hid sub.subTHoles)
  ty@(TNeu md id List.Nil) -> applySubType sub $ maybe ty identity (Map.lookup id sub.subTypeVars)
  TNeu md id args -> TNeu md id ((\(TypeArg md ty) -> TypeArg md (applySubType sub ty)) <$> args)

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
