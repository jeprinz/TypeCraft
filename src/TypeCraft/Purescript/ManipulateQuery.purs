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
import TypeCraft.Purescript.Grammar (Type(..), Kind(..), PolyType(..), Term(..), TermVarID, Tooth(..), freshTHole, freshTermBind, freshTypeHoleID)
import TypeCraft.Purescript.MD (defaultLambdaMD, defaultVarMD)
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
                -- get the type of the var, and create holes for all the arguments
                tell [ [ CompletionTerm $ fillNeutral pty id ty ] ]
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- lam
      when (str `kindaStartsWith` "lam")
        $ tell [ [ CompletionPath $ List.fromFoldable [ Lambda3 defaultLambdaMD (freshTermBind Nothing) (freshTHole unit) (freshTHole unit) ] ] ]
  _ -> [] -- TODO: impl

-- TODO: do properly
fillNeutral :: PolyType -> TermVarID -> Type -> Term
fillNeutral pty id ty = Var defaultVarMD id (List.fromFoldable [])
