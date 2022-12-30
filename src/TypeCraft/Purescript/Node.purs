module TypeCraft.Purescript.Node where

import Prelude
import TypeCraft.Purescript.State (State)
import TypeCraft.Purescript.Nullable (Nullable, fromMaybe, pureNullable)
import Data.Maybe (Maybe)

-- Node
foreign import data Node :: Type

foreign import makeNode_ ::
  { dat :: NodeData
  , kids :: Array (Array Node)
  , getCursor :: Nullable (Unit -> State)
  , getSelect :: Nullable (Unit -> State)
  , style :: NodeStyle
  } ->
  Node

makeNode ::
  { dat :: NodeData
  , kids :: Array (Array Node)
  , getCursor :: Maybe (Unit -> State)
  , getSelect :: Maybe (Unit -> State)
  , style :: NodeStyle
  } ->
  Node
makeNode x =
  makeNode_
    { dat: x.dat
    , kids: x.kids
    , getCursor: fromMaybe x.getCursor
    , getSelect: fromMaybe x.getSelect
    , style: x.style
    }

-- NodeData
foreign import data NodeData :: Type

foreign import data NodeIndentation :: Type
foreign import makeInlineNodeIndentation :: NodeIndentation
foreign import makeNewlineNodeIndentation :: NodeIndentation -- doesn't indent
foreign import makeIndentNodeIndentation :: NodeIndentation

foreign import makeNodeData_ ::
  { indentation :: NodeIndentation
  , isParenthesized :: Boolean
  , label :: Nullable String
  } ->
  NodeData

makeNodeData ::
  { indentation :: NodeIndentation
  , isParenthesized :: Boolean
  , label :: String
  } ->
  NodeData
makeNodeData { indentation, isParenthesized, label } =
  makeNodeData_
    { indentation
    , isParenthesized
    , label: pureNullable label
    }

-- NodeStyle
foreign import data NodeStyle :: Type

foreign import makeNormalNodeStyle :: NodeStyle

foreign import makeCursorNodeStyle :: NodeStyle

foreign import makeSelectTopNodeStyle :: NodeStyle

foreign import makeSelectBotNodeStyle :: NodeStyle

foreign import makeQueryInsertTopStyle :: NodeStyle

foreign import makeQueryInsertBotNodeStyle :: NodeStyle

foreign import makeQueryReplaceNewNodeStyle :: NodeStyle

foreign import makeQueryReplaceOldNodeStyle :: NodeStyle

foreign import makeQueryInvalidNodeStyle :: String -> NodeStyle
