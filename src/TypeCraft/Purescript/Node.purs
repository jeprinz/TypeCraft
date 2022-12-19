module TypeCraft.Purescript.Node where

import Prelude
import TypeCraft.Purescript.State
import Data.Maybe (Maybe, maybe)

data Select  -- TODO: jacob needs to define stuff  for this 

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

-- Nullable
foreign import data Nullable :: Type -> Type

foreign import emptyNullable :: forall a. Nullable a

foreign import pureNullable :: forall a. a -> Nullable a

nullableMaybe :: forall a. Maybe a -> Nullable a
nullableMaybe = maybe emptyNullable pureNullable
