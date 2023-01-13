module TypeCraft.Purescript.ManipulateQuery where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String
import Debug (traceM)
import TypeCraft.Purescript.ManipulateString (isIgnoreKey, manipulateString)
import TypeCraft.Purescript.State (Query, State, CursorMode)

isNonemptyQueryString :: Query -> Boolean
isNonemptyQueryString query = not $ String.null query.string

manipulateQuery :: String -> State -> CursorMode -> Maybe Query
manipulateQuery key st cursorMode@{ query: query@{ string, completion_i, completionOption_i } }
  | key == "ArrowUp" && isNonemptyQueryString query = pure query { completion_i = completion_i - 1 }
  | key == "ArrowDown" && isNonemptyQueryString query = pure query { completion_i = completion_i + 1 }
  | key == "ArrowLeft" && isNonemptyQueryString query = pure query { completionOption_i = query.completionOption_i - 1 }
  | key == "ArrowRight" && isNonemptyQueryString query = pure query { completionOption_i = query.completionOption_i + 1 }
  | otherwise = do
    traceM $ "manipulateQuery.key = " <> key
    string' <- manipulateString key string
    pure query { string = string' }
