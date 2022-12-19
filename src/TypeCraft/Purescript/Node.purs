module TypeCraft.Purescript.Node where

import Prelude
import TypeCraft.Purescript.State
import TypeCraft.Purescript.Nullable
import Data.Maybe (Maybe, maybe)

-- Node
foreign import data Node :: Type

foreign import makeNode ::
  { dat :: NodeData
  , kids :: Array (Array Node)
  , getCursor :: Unit -> CursorLocation
  , isCursorable :: Boolean
  , getSelect :: Unit -> Select
  , isSelectable :: Boolean
  , style :: NodeStyle
  } ->
  Node

-- NodeData
foreign import data NodeData :: Type

foreign import makeNodeData ::
  { indentation :: Nullable Int
  , isParenthesized :: Boolean
  , label :: Nullable String
  } ->
  NodeData

makeNodeDataSane ::
  { indentation :: Int
  , isParenthesized :: Boolean
  , label :: String
  } ->
  NodeData
makeNodeDataSane {indentation, isParenthesized, label}
    = makeNodeData {
        indentation: pureNullable indentation
        , isParenthesized
        , label: pureNullable label}

-- NodeStyle
foreign import data NodeStyle :: Type

foreign import makeCursorNodeStyle :: NodeStyle

foreign import makeSelectTopNodeStyle :: NodeStyle

foreign import makeSelectBotNodeStyle :: NodeStyle

foreign import makeQueryInsertTopStyle :: NodeStyle

foreign import makeQueryInsertBotNodeStyle :: NodeStyle

foreign import makeQueryReplaceNewNodeStyle :: NodeStyle

foreign import makeQueryReplaceOldNodeStyle :: NodeStyle

foreign import makeQueryInvalidNodeStyle :: String -> NodeStyle

