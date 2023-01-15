module TypeCraft.Purescript.ManipulateQuery where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)

import Data.Array.NonEmpty as Array
import Data.Either (either)
import Data.Foldable (and, traverse_)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.String as String
import Data.Tuple (fst, snd)
import Data.UUID (UUID)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Change(..), Kind(..), PolyType(..), Term(..), TermVarID, Tooth(..), Type(..), TypeHoleID, TypeVarID, freshHole, freshTHole, freshTermBind, freshTypeHoleID)
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
    execWriter do
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
                  Nothing -> pure unit
                  Just ((ty' /\ tm') /\ sub) -> tell [ [ CompletionTerm tm' (applySubType sub ty') ] ]
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- lam
      when (str `kindaStartsWith` "lam")
        $ tell
            [ [ let
                  alpha = freshTHole unit
                in
                  -- lam (~ : alpha) ↦ ({} : ty)
                  CompletionTermPath
                    (List.fromFoldable [ Lambda3 defaultLambdaMD (freshTermBind Nothing) alpha ty ])
                    (Plus alpha (Replace ty ty))
              ]
            ]
      -- let
      when (str `kindaStartsWith` "let")
        $ tell
            [ [ -- let ~<∅> : alpha = ? in {} : ty
                CompletionTermPath
                  (List.fromFoldable [ Let5 defaultLetMD (freshTermBind Nothing) List.Nil (freshHole unit) (freshTHole unit) ty ])
                  (Replace ty ty)
              ]
            ]
  _ -> [] -- TODO: impl

-- * unification
type Unify a
  = StateT Sub (Except String) a

type Sub
  = { subTypeVars :: Map.Map TypeVarID Type
    , subTHoles :: Map.Map TypeHoleID Type
    }

applySubType :: Sub -> Type -> Type
applySubType = hole' "applySubType"

emptySub :: Sub
emptySub = { subTypeVars: Map.empty, subTHoles: Map.empty }

runUnify :: forall a. Unify a -> Maybe (a /\ Sub)
runUnify m = either (const Nothing) pure $ runExcept (runStateT m emptySub)

unify :: Type -> Type -> Unify Type
unify ty1 ty2 = case ty1 /\ ty2 of 
  THole md hid  /\ _ -> hole' "TODO: check occurences of hid in ty2, sub hid for ty2, pure ty2"
  _ /\ THole md hid -> hole' "TODO: check occurences of hid in ty1, sub hid for ty1, pure ty1"
  _ 
    | ty1 == ty2 -> pure ty1
    | otherwise -> throwError $ "types do not unify: (" <> show ty1 <> ") ~ (" <> show ty2 <> ")"


-- create neutral form from variable of first type that can fill the hole of the
-- second type 
-- TODO: do properly
fillNeutral :: PolyType -> TermVarID -> Type -> Unify (Type /\ Term)
fillNeutral pty id ty = case pty of
  Forall _ pty' -> fillNeutral pty' id ty
  PType ty' -> fillNeutral' ty' id ty

fillNeutral' :: Type -> TermVarID -> Type -> Unify (Type /\ Term)
fillNeutral' ty id ty' = case ty of
  -- TODO: generate args for neu
  -- Arrow md ty1 ty2 ->
  --   (\tm -> App defaultAppMD tm (freshHole unit) ty1 ?a)
  --   <$> fillNeutral' ty2 id ty'
  _ -> hole' "fillNeutral'" -- pure $ Var defaultVarMD id (List.fromFoldable []) -- TODO: obv wrong
