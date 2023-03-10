module TypeCraft.Purescript.ManipulateQuery where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.State (CursorMode, Query, State)
import Data.List as List
import Data.Maybe (Maybe)
import Data.String as String
import TypeCraft.Purescript.Completions (calculateCompletionGroups)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.ManipulateString (manipulateString)

isNonemptyQueryString :: Query -> Boolean
isNonemptyQueryString query = not $ String.null query.string

manipulateQuery :: Key -> State -> CursorMode -> Maybe Query
manipulateQuery key st cursorMode@{ query: query@{ string, completionGroup_i, completionGroupItem_i } }
  | key.key == "ArrowUp" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i - 1 }
  | key.key == "ArrowDown" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i + 1 }
  | key.key == "ArrowLeft" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i - 1 }
  | key.key == "ArrowRight" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i + 1 }
  | otherwise = do
    string' <- manipulateString key string
    let
      complGroups = calculateCompletionGroups st cursorMode

      matchComplGroups =
        flip List.foldMap complGroups \{ filterLabel, completions } ->
          if filterLabel string' then
            [ completions <*> [ string' ] ]
          else
            []
    pure
      query
        { string = string'
        , completionGroup_i = 0
        , completionGroupItem_i = 0
        , completionGroups = matchComplGroups
        }
