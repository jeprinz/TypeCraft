module TypeCraft.Purescript.Node where

import Prelude
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
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

foreign import getNodeData :: Node -> NodeData

foreign import data NodeTag_ :: Type

foreign import makeNodeTag_ :: String -> NodeTag_

foreign import fromNodeTag_ :: NodeTag_ -> String

readNodeTag :: String -> NodeTag
readNodeTag str
  | str == "ty arr" = ArrowNodeTag
  | str == "ty hol" = THoleNodeTag
  | str == "ty neu" = TNeuNodeTag
  | str == "poly-ty forall" = ForallNodeTag
  | str == "poly-ty ty" = PTypeNodeTag
  | str == "ty-arg" = TypeArgNodeTag
  | str == "tm app" = AppNodeTag
  | str == "tm lam" = LambdaNodeTag
  | str == "tm var" = VarNodeTag
  | str == "tm let" = LetNodeTag
  | str == "tm dat" = DataNodeTag
  | str == "tm ty-let" = TLetNodeTag
  | str == "tm ty-boundary" = TypeBoundaryNodeTag
  | str == "tm cx-boundary" = ContextBoundaryNodeTag
  | str == "tm hol" = HoleNodeTag
  | str == "tm buf" = BufferNodeTag
  | str == "ty-bnd" = TypeBindNodeTag
  | str == "tm-bnd" = TermBindNodeTag
  | str == "ctr-prm" = CtrParamNodeTag
  | str == "ctr" = ConstructorNodeTag
  | str == "ty-arg-list cons" = TypeArgListConsNodeTag
  | str == "ty-arg-list nil" = TypeArgListNilNodeTag
  | str == "ty-arg-list cons" = TypeBindListConsNodeTag
  | str == "ty-arg-list nil" = TypeBindListNilNodeTag
  | str == "ctr-list cons" = ConstructorListConsNodeTag
  | str == "ctr-list nil" = ConstructorListNilNodeTag
  | str == "ctr-param-list cons" = CtrParamListConsNodeTag
  | str == "ctr-param-list nil" = CtrParamListNilNodeTag
  | otherwise = unsafeThrow $ "invalid NodeTag: " <> str

data NodeTag
  -- NodeTag: Type
  = ArrowNodeTag
  | THoleNodeTag
  | TNeuNodeTag
  -- NodeTag: PolyType
  | ForallNodeTag
  | PTypeNodeTag
  -- NodeTag: TypeArg
  | TypeArgNodeTag
  -- NodeTag: Term
  | AppNodeTag
  | LambdaNodeTag
  | VarNodeTag
  | LetNodeTag
  | DataNodeTag
  | TLetNodeTag
  | TypeBoundaryNodeTag
  | ContextBoundaryNodeTag
  | HoleNodeTag
  | BufferNodeTag
  -- NodeTag: TypeBind
  | TypeBindNodeTag
  -- NodeTag: TermBind
  | TermBindNodeTag
  -- NodeTag: CtrParam
  | CtrParamNodeTag
  -- NodeTag: Constructor
  | ConstructorNodeTag
  -- NodeTag: List TypeArg
  | TypeArgListConsNodeTag
  | TypeArgListNilNodeTag
  -- NodeTag: List TypeBind
  | TypeBindListConsNodeTag
  | TypeBindListNilNodeTag
  -- NodeTag: List Constructor
  | ConstructorListConsNodeTag
  | ConstructorListNilNodeTag
  -- NodeTag: List CtrParam
  | CtrParamListConsNodeTag
  | CtrParamListNilNodeTag

foreign import getNodeTag_ :: NodeData -> NodeTag_

getNodeTag :: NodeData -> NodeTag
getNodeTag = getNodeTag_ >>> fromNodeTag_ >>> readNodeTag

getNodeDataTag :: Node -> NodeTag
getNodeDataTag = getNodeData >>> getNodeTag

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

-- utilities
setIndentNodeIndentationIf :: Boolean -> Node -> Node
setIndentNodeIndentationIf =
  if _ then
    setNodeIndentation makeIndentNodeIndentation
  else
    identity

calculateNodeIndentation :: NodeTag -> NodeTag -> NodeIndentation
calculateNodeIndentation parentTag childTag = makeInlineNodeIndentation

calculateNodeIsParenthesized :: NodeTag -> NodeTag -> Boolean
calculateNodeIsParenthesized parentTag childTag = false

setCalculatedNodeData :: NodeTag -> Node -> Node
setCalculatedNodeData parentTag childNode =
  let
    childTag = getNodeDataTag childNode

    indentation = calculateNodeIndentation parentTag childTag

    isParenthesized = calculateNodeIsParenthesized parentTag childTag
  in
    childNode
      # setNodeParenthesized isParenthesized
      >>> setNodeIndentation indentation

setNodeLabelMaybe :: Maybe String -> Node -> Node
setNodeLabelMaybe (Just label) = setNodeLabel label

setNodeLabelMaybe Nothing = identity
