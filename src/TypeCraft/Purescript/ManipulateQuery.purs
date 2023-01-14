module TypeCraft.Purescript.ManipulateQuery where

import Control.Monad.Writer
import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Data.Array.NonEmpty as Array
import Data.Foldable (and, traverse_)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.String as String
import Data.UUID (UUID)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Kind(..), PolyType(..), Term(..), TermVarID, Tooth(..), Type(..), freshHole, freshTHole, freshTermBind, freshTypeHoleID)
import TypeCraft.Purescript.MD (defaultAppMD, defaultLambdaMD, defaultVarMD)
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
                case fillNeutral pty id ty of
                  Nothing -> pure unit
                  Just tm -> tell [ [ CompletionTerm tm ] ]
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- lam
      when (str `kindaStartsWith` "lam")
        $ tell [ [ CompletionPath $ List.fromFoldable [ Lambda3 defaultLambdaMD (freshTermBind Nothing) (freshTHole unit) ty ] ] ]
  _ -> [] -- TODO: impl

-- create neutral form from variable of first type that can fill the hole of the
-- second type 
-- TODO: do properly
fillNeutral :: PolyType -> TermVarID -> Type -> Maybe Term
fillNeutral pty id ty = case pty of
  Forall _ pty' -> fillNeutral pty' id ty
  PType ty' -> fillNeutral' ty' id ty

fillNeutral' :: Type -> TermVarID -> Type -> Maybe Term
fillNeutral' ty id ty' = case ty of
  -- TODO: generate args for neu
  -- Arrow md ty1 ty2 ->
  --   (\tm -> App defaultAppMD tm (freshHole unit) ty1 ?a)
  --   <$> fillNeutral' ty2 id ty'
  _ -> pure $ Var defaultVarMD id (List.fromFoldable []) -- TODO: obv wrong
