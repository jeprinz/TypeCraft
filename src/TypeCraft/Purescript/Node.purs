module TypeCraft.Purescript.Node where

import Control.Alternative
import Control.Applicative
import Prelude
import Prim hiding (Type)
import Data.Array (find)
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class BoundedEnum, class Enum, cardinality, enumFromTo)
import Data.Enum.Generic (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Foldable (foldr)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Debug as Debug
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Nullable (Nullable)
import TypeCraft.Purescript.Nullable as Nullable
import TypeCraft.Purescript.State (State)
import TypeCraft.Purescript.Util (hole, hole')
import Data.List (List(..), (:))

-- Node
foreign import data Node :: Prim.Type

foreign import makeNode_ ::
  { kids :: Array Node
  , getCursor :: Nullable (State -> State)
  , getSelect :: Nullable (State -> State)
  , style :: NodeStyle
  , indentation :: NodeIndentation
  , isParenthesized :: Boolean
  , tag :: NodeTag_
  , label :: Nullable String -- requires: Term.Var, TermBind
  , queryString :: Nullable String -- requires: active query
  , completions :: Nullable (Array Node) -- requires: active query
  , activeCompletion :: Nullable Int -- requires: active query
  } ->
  Node

makeNode ::
  { kids :: Array Node
  , getCursor :: Maybe (State -> State)
  , getSelect :: Maybe (State -> State)
  , tag :: NodeTag
  } ->
  Node
makeNode x =
  makeNode_
    { kids: x.kids
    , getCursor: Nullable.fromMaybe x.getCursor
    , getSelect: Nullable.fromMaybe x.getSelect
    , style: makeNormalNodeStyle
    , indentation: makeInlineNodeIndentation
    , isParenthesized: false
    , label: Nullable.emptyNullable
    , queryString: Nullable.emptyNullable
    , completions: Nullable.emptyNullable
    , activeCompletion: Nullable.emptyNullable
    , tag: toNodeTag_ x.tag
    }

foreign import setNodeStyle :: NodeStyle -> Node -> Node

foreign import setNodeIndentation :: NodeIndentation -> Node -> Node

foreign import setNodeIsParenthesized :: Boolean -> Node -> Node

foreign import setNodeLabel :: String -> Node -> Node

foreign import setNodeQueryString :: String -> Node -> Node

foreign import setNodeCompletions :: Array Node -> Number -> Node -> Node

-- NodeIndentation
foreign import data NodeIndentation :: Prim.Type

foreign import makeInlineNodeIndentation :: NodeIndentation

foreign import makeNewlineNodeIndentation :: NodeIndentation -- doesn't indent

foreign import makeIndentNodeIndentation :: NodeIndentation

-- NodeTag & NodeTag_
foreign import data NodeTag_ :: Prim.Type

foreign import makeNodeTag_ :: String -> NodeTag_

foreign import fromNodeTag_ :: NodeTag_ -> String

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
  -- Change
  | ReplaceNodeTag
  | PlusNodeTag
  | MinusNodeTag

derive instance eqNodeTag :: Eq NodeTag

derive instance ordNodeTag :: Ord NodeTag

derive instance genericNodeTag :: Generic NodeTag _

instance enumNodeTag :: Enum NodeTag where
  succ x = genericSucc x
  pred x = genericPred x

instance boundedNodeTag :: Bounded NodeTag where
  top = genericTop
  bottom = genericBottom

instance boundedEnumNodeTag :: BoundedEnum NodeTag where
  cardinality = genericCardinality
  toEnum x = genericToEnum x
  fromEnum x = genericFromEnum x

-- iterate through all of the NodeTags until find one that has matching label
-- (produced by `fromNodeTag_`)
readNodeTag :: String -> NodeTag
readNodeTag str = case find (toNodeTag_ >>> fromNodeTag_ >>> (_ == str)) (enumFromTo bottom top) of
  Nothing -> unsafeThrow $ "invalid NodeTag: " <> str
  Just tag -> tag

toNodeTag_ :: NodeTag -> NodeTag_
toNodeTag_ = case _ of
  ArrowNodeTag -> makeNodeTag_ "ty arr"
  THoleNodeTag -> makeNodeTag_ "ty hol"
  TNeuNodeTag -> makeNodeTag_ "ty neu"
  ForallNodeTag -> makeNodeTag_ "poly-ty forall"
  PTypeNodeTag -> makeNodeTag_ "poly-ty ty"
  TypeArgNodeTag -> makeNodeTag_ "ty-arg"
  AppNodeTag -> makeNodeTag_ "tm app"
  LambdaNodeTag -> makeNodeTag_ "tm lam"
  VarNodeTag -> makeNodeTag_ "tm var"
  LetNodeTag -> makeNodeTag_ "tm let"
  DataNodeTag -> makeNodeTag_ "tm dat"
  TLetNodeTag -> makeNodeTag_ "tm ty-let"
  TypeBoundaryNodeTag -> makeNodeTag_ "tm ty-boundary"
  ContextBoundaryNodeTag -> makeNodeTag_ "tm cx-coundary"
  HoleNodeTag -> makeNodeTag_ "tm hol"
  BufferNodeTag -> makeNodeTag_ "tm buf"
  TypeBindNodeTag -> makeNodeTag_ "ty-bnd"
  TermBindNodeTag -> makeNodeTag_ "tm-bnd"
  CtrParamNodeTag -> makeNodeTag_ "ctr-prm"
  ConstructorNodeTag -> makeNodeTag_ "ctr"
  TypeArgListConsNodeTag -> makeNodeTag_ "ty-arg-list cons"
  TypeArgListNilNodeTag -> makeNodeTag_ "ty-arg-list nil"
  TypeBindListConsNodeTag -> makeNodeTag_ "ty-bnd-list cons"
  TypeBindListNilNodeTag -> makeNodeTag_ "ty-bnd-list nil"
  ConstructorListConsNodeTag -> makeNodeTag_ "ctr-list cons"
  ConstructorListNilNodeTag -> makeNodeTag_ "ctr-list nil"
  CtrParamListConsNodeTag -> makeNodeTag_ "ctr-prm-list cons"
  CtrParamListNilNodeTag -> makeNodeTag_ "ctr-prm-list nil"
  ReplaceNodeTag -> makeNodeTag_ "replace"
  PlusNodeTag -> makeNodeTag_ "plus"
  MinusNodeTag -> makeNodeTag_ "minus"

foreign import getNodeTag_ :: Node -> NodeTag_

getNodeTag :: Node -> NodeTag
getNodeTag = getNodeTag_ >>> fromNodeTag_ >>> readNodeTag

termToNodeTag :: Term -> NodeTag
termToNodeTag = case _ of
  App _ _ _ _ _ -> AppNodeTag
  Lambda _ _ _ _ _ -> LambdaNodeTag
  Var _ _ _ -> VarNodeTag
  Let _ _ _ _ _ _ _ -> LetNodeTag
  Data _ _ _ _ _ _ -> DataNodeTag
  TLet _ _ _ _ _ _ -> TLetNodeTag
  TypeBoundary _ _ _ -> TypeBoundaryNodeTag
  ContextBoundary _ _ _ _ -> ContextBoundaryNodeTag
  Hole _ -> HoleNodeTag
  Buffer _ _ _ _ _ -> BufferNodeTag

ctrListToNodeTag :: List Constructor -> NodeTag
ctrListToNodeTag Nil = ConstructorListNilNodeTag
ctrListToNodeTag (_ : _) = ConstructorListConsNodeTag

typeToNodeTag :: Type -> NodeTag
typeToNodeTag = case _ of
    Arrow _ _ _ -> ArrowNodeTag
    THole _ _ -> THoleNodeTag
    TNeu _ _ _ -> TNeuNodeTag

-- NodeStyle
foreign import data NodeStyle :: Prim.Type

foreign import makeNormalNodeStyle :: NodeStyle

foreign import makeCursorNodeStyle :: NodeStyle

foreign import makeSelectTopNodeStyle :: NodeStyle

foreign import makeSelectBotNodeStyle :: NodeStyle

foreign import makeQueryInsertTopStyle :: NodeStyle

foreign import makeQueryInsertBotNodeStyle :: NodeStyle

foreign import makeQueryReplaceNewNodeStyle :: NodeStyle

foreign import makeQueryReplaceOldNodeStyle :: NodeStyle

foreign import makeQueryInvalidNodeStyle :: NodeStyle

foreign import makeQueryMetaholeNodeStyle :: NodeStyle

-- utilities
setIndentNodeIndentationIf :: Boolean -> Node -> Node
setIndentNodeIndentationIf =
  if _ then
    setNodeIndentation makeIndentNodeIndentation
  else
    identity

calculateNodeIsParenthesized :: NodeTag -> NodeTag -> Boolean
calculateNodeIsParenthesized parentTag childTag = false -- hole' "calculateNodeIsParenthesized"

setCalculatedNodeIsParenthesized :: NodeTag -> Node -> Node
setCalculatedNodeIsParenthesized parentTag child = setNodeIsParenthesized (calculateNodeIsParenthesized parentTag (getNodeTag child)) child

-- # setNodeIsParenthesized isParenthesized
-- >>> setNodeIndentation indentation
setNodeLabelMaybe :: Maybe String -> Node -> Node
setNodeLabelMaybe (Just label) = setNodeLabel label

setNodeLabelMaybe Nothing = identity
