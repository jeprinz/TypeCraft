module TypeCraft.Purescript.Node where

import Prelude

import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Nullable (Nullable)
import TypeCraft.Purescript.Nullable as Nullable
import TypeCraft.Purescript.State (State)

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
  } ->
  Node
makeNode x =
  makeNode_
    { dat: x.dat
    , kids: x.kids
    , getCursor: Nullable.fromMaybe x.getCursor
    , getSelect: Nullable.fromMaybe x.getSelect
    , style: makeNormalNodeStyle
    }

foreign import setNodeStyle :: NodeStyle -> Node -> Node

foreign import setNodeIndentation :: NodeIndentation -> Node -> Node

foreign import setNodeParenthesized :: Boolean -> Node -> Node

foreign import setNodeLabel :: String -> Node -> Node

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
  , tag :: NodeTag
  } ->
  NodeData

makeNodeData ::
  { tag :: NodeTag
  } ->
  NodeData
makeNodeData { tag } =
  makeNodeData_
    { indentation: makeInlineNodeIndentation
    , isParenthesized: false
    , label: Nullable.fromMaybe Nothing
    , tag
    }

-- NodeTag
foreign import data NodeTag :: Type

-- NodeTag: Type
foreign import makeArrowNodeTag :: NodeTag

foreign import makeTHoleNodeTag :: NodeTag

foreign import makeTNeuNodeTag :: NodeTag

-- NodeTag: PolyType
foreign import makeForallNodeTag :: NodeTag

foreign import makePTypeNodeTag :: NodeTag

-- NodeTag: TypeArg
foreign import makeTypeArgNodeTag :: NodeTag

-- NodeTag: Term
foreign import makeAppNodeTag :: NodeTag

foreign import makeLambdaNodeTag :: NodeTag

foreign import makeVarNodeTag :: NodeTag

foreign import makeLetNodeTag :: NodeTag

foreign import makeDataNodeTag :: NodeTag

foreign import makeTLetNodeTag :: NodeTag

foreign import makeTypeBoundaryNodeTag :: NodeTag

foreign import makeContextBoundaryNodeTag :: NodeTag

foreign import makeHoleNodeTag :: NodeTag

foreign import makeBufferNodeTag :: NodeTag

-- NodeTag: TypeBind
foreign import makeTypeBindNodeTag :: NodeTag

-- NodeTag: TermBind
foreign import makeTermBindNodeTag :: NodeTag

-- NodeTag: CtrParam
foreign import makeCtrParamNodeTag :: NodeTag

-- NodeTag: Constructor
foreign import makeConstructorNodeTag :: NodeTag

-- NodeTag: List TypeArg
foreign import makeTypeArgListConsNodeTag :: NodeTag

foreign import makeTypeArgListNilNodeTag :: NodeTag

-- NodeTag: List TypeBind
foreign import makeTypeBindListConsNodeTag :: NodeTag

foreign import makeTypeBindListNilNodeTag :: NodeTag

-- NodeTag: List Constructor
foreign import makeConstructorListConsNodeTag :: NodeTag

foreign import makeConstructorListNilNodeTag :: NodeTag

-- NodeTag: List CtrParam
foreign import makeCtrParamListConsNodeTag :: NodeTag

foreign import makeCtrParamListNilNodeTag :: NodeTag

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
