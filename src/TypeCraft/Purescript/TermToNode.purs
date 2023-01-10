module TypeCraft.Purescript.TermToNode where

import Prelude
import Prim hiding (Type)

import Data.List ((:))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe', maybe')
import Debug (trace)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Constructor, TermBind(..), Tooth(..), UpPath)
import TypeCraft.Purescript.Node (Node, NodeTag(..), makeNode, setCalculatedNodeData, setNodeLabel, setNodeLabelMaybe)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode, makeState)
import TypeCraft.Purescript.TermRec (ListCtrParamRecValue, ListTypeArgRecValue, ListTypeBindRecValue, TermBindRecValue, TermRecValue, TypeArgRecValue, TypeBindRecValue, TypeRecValue, ListCtrRecValue, recTerm, recType)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Node (setNodeIndentation)
import TypeCraft.Purescript.Node (makeIndentNodeIndentation)

data AboveInfo
  = AICursor UpPath
  | AISelect UpPath UpPath -- top path, then middle path

stepAI :: Tooth -> AboveInfo -> AboveInfo
stepAI tooth (AICursor path) = AICursor (tooth : path)

stepAI tooth (AISelect topPath middlePath) = AISelect topPath (tooth : middlePath)

aIOnlyCursor :: AboveInfo -> AboveInfo
aIOnlyCursor (AICursor path) = AICursor path

aIOnlyCursor (AISelect topPath middlePath) = AICursor (middlePath <> topPath)

aIGetPath :: AboveInfo -> UpPath
aIGetPath (AICursor path) = path

aIGetPath (AISelect top middle) = middle <> top

indentIf :: Boolean -> Node -> Node
indentIf false n = n
indentIf true n = setNodeIndentation makeIndentNodeIndentation n

-- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?
-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: AboveInfo -> TermRecValue -> Node
termToNode aboveInfo term =
  let
    nodeInfo =
      recTerm
        ( { lambda:
              \md tBind ty body bodyTy ->
                { tag: LambdaNodeTag
                , label: Nothing
                , kids:
                    [ termBindToNode (stepAI (Lambda1 md ty.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tBind
                    , typeToNode (stepAI (Lambda2 md tBind.tBind body.term bodyTy) (aIOnlyCursor aboveInfo)) ty
                    , termToNode (stepAI (Lambda3 md tBind.tBind ty.ty bodyTy) aboveInfo) body
                    ]
                }
          , app:
              \md t1 t2 argTy outTy ->
                { tag: AppNodeTag
                , label: Nothing
                , kids:
                    [ termToNode (stepAI (App1 md t2.term argTy outTy) aboveInfo) t1
                    , termToNode (stepAI (App2 md t2.term argTy outTy) aboveInfo) t2
                    ]
                }
          , var:
              \md x targs ->
                let
                  label =
                    fromMaybe'
                      (\_ -> unsafeThrow $ "variable index not found: " <> show x)
                      $ Map.lookup x term.ctxs.mdctx
                in
                  { tag: VarNodeTag
                  , label: Just label
                  , kids: []
                  }
          , lett:
              \md tBind tyBinds def defTy body bodyTy ->
                { tag: LetNodeTag
                , label: Nothing
                , kids:
                    [ termBindToNode (stepAI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) aboveInfo) tBind
                    , typeBindListToNode (stepAI (Let2 md tBind.tBind {-List TypeBind-} def.term defTy.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tyBinds
                    , termToNode (stepAI (Let3 md tBind.tBind tyBinds.tyBinds defTy.ty body.term bodyTy) aboveInfo) def
                    , typeToNode (stepAI (Let4 md tBind.tBind tyBinds.tyBinds def.term body.term bodyTy) (aIOnlyCursor aboveInfo)) defTy
                    , indentIf md.bodyIndented $ termToNode (stepAI (Let5 md tBind.tBind tyBinds.tyBinds def.term defTy.ty bodyTy) aboveInfo) body
                    ]
                }
          , dataa:
              \md x tbinds ctrs body bodyTy ->
                { tag: DataNodeTag
                , label: Nothing
                , kids:
                    [ typeBindToNode (stepAI (Data1 md tbinds.tyBinds ctrs.ctrs term.term bodyTy) aboveInfo) x
                    , typeBindListToNode (stepAI (Data2 md x.tyBind ctrs.ctrs term.term bodyTy) aboveInfo) tbinds
                    , constructorListToNode (stepAI (Data3 md x.tyBind tbinds.tyBinds term.term bodyTy) aboveInfo) ctrs
                    , termToNode (stepAI (Data4 md x.tyBind tbinds.tyBinds ctrs.ctrs bodyTy) aboveInfo) body
                    ]
                }
          , tlet: \md x tbinds def body bodyTy -> hole' "termToNode"
          , typeBoundary:
              \md c t ->
                { tag: TypeBoundaryNodeTag
                , label: Nothing
                , kids: [ termToNode (stepAI (TypeBoundary1 md c) aboveInfo) t ]
                }
          , contextBoundary:
              \md x c t ->
                { tag: ContextBoundaryNodeTag
                , label: Nothing
                , kids: [ termToNode (stepAI (ContextBoundary1 md x c) aboveInfo) t ]
                }
          , hole:
              \md ->
                { tag: HoleNodeTag
                , label: Nothing
                , kids: []
                }
          , buffer:
              \md def defTy body bodyTy ->
                { tag: BufferNodeTag
                , label: Nothing
                , kids:
                    [ termToNode (stepAI (Buffer1 md defTy.ty body.term bodyTy) aboveInfo) def
                    , typeToNode (stepAI (Buffer2 md def.term body.term bodyTy) aboveInfo) defTy
                    , termToNode (stepAI (Buffer3 md def.term defTy.ty bodyTy) aboveInfo) body
                    ]
                }
          }
        )
        term
  in
    -- pieces that are the same for every syntactic form are done here:
    setNodeLabelMaybe nodeInfo.label
      $ makeNode
          { kids: nodeInfo.kids <#> setCalculatedNodeData nodeInfo.tag >>> pure
          , getCursor: Just \_ -> 
              trace ("termToNode.aIGetPath aboveInfo = " <> show (aIGetPath aboveInfo)) \_ ->
              makeState $ makeCursorMode $ TermCursor term.ctxs term.ty (aIGetPath aboveInfo) term.term
          , getSelect:
              case aboveInfo of
                AICursor _path -> Nothing -- TODO: impl select
                AISelect top middle -> Just \_ -> makeState $ SelectMode $ TermSelect term.ctxs (hole' "termToNode") term.ty middle top term.term
          , tag: nodeInfo.tag
          }

typeToNode :: AboveInfo -> TypeRecValue -> Node
typeToNode aboveInfo ty =
  let
    nodeInfo =
      recType
        ( { arrow:
              \md ty1 ty2 ->
                { tag: ArrowNodeTag
                , kids:
                    [ typeToNode (stepAI (Arrow1 md ty2.ty) aboveInfo) ty1
                    , typeToNode (stepAI (Arrow2 md ty1.ty) aboveInfo) ty2
                    ]
                }
          , tHole:
              \md x ->
                { tag: THoleNodeTag
                , kids: []
                }
          , tNeu:
              \md x tyArgs ->
                { tag: TNeuNodeTag
                , kids: [] -- TODO: Put type parameters
                }
          }
        )
        ty
  in
    makeNode
      { kids: nodeInfo.kids <#> pure
      , getCursor: Just \_ -> 
          trace ("typeToNode.aIGetPath aboveInfo = " <> show (aIGetPath aboveInfo)) \_ ->
          makeState $ makeCursorMode $ TypeCursor ty.ctxs (aIGetPath aboveInfo) ty.ty
      , getSelect:
          case aboveInfo of
            AICursor path -> Nothing -- TODO: impl select
            AISelect top middle -> Just \_ -> makeState $ SelectMode $ TypeSelect ty.ctxs false top middle ty.ty
      , tag: nodeInfo.tag
      }

ctrListToNode :: AboveInfo -> ListCtrRecValue -> Node
ctrListToNode aboveInfo ctrs = hole' "ctrListToNode"

ctrToNode :: AboveInfo -> Constructor -> Node
ctrToNode aboveInfo ctr = hole' "ctrToNode"

--ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
--ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
--    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
--    , kids: [[typeToNode (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
--    , getCursor: Nothing
--    , getSelect: Nothing
--    , style: makeNormalNodeStyle
--}
typeArgToNode :: AboveInfo -> TypeArgRecValue -> Node
typeArgToNode aboveInfo tyArg = hole' "typeArgToNode"

typeBindToNode :: AboveInfo -> TypeBindRecValue -> Node
typeBindToNode aboveInfo tyBind = hole' "typeBindToNode"

typeBindListToNode :: AboveInfo -> ListTypeBindRecValue -> Node
typeBindListToNode aboveInfo tyBinds = -- TODO: write actual implementation
     makeNode {
        tag: TypeBindListNilNodeTag
        , kids: [[]]
        , getCursor: Nothing
        , getSelect: Nothing
    }

termBindToNode :: AboveInfo -> TermBindRecValue -> Node
termBindToNode aboveInfo { ctxs, tBind: tBind@(TermBind md x) } =
  setNodeLabel md.varName
    $ makeNode
        { kids: []
        , getCursor: Just \_ -> 
              trace ("termBindToNode.aIGetPath aboveInfo = " <> show (aIGetPath aboveInfo)) \_ ->
              makeState $ makeCursorMode $ TermBindCursor ctxs (aIGetPath aboveInfo) tBind
        , getSelect: Nothing
        , tag: TermBindNodeTag
        }

ctrParamListToNode :: AboveInfo -> ListCtrParamRecValue -> Node
ctrParamListToNode aboveInfo ctrParams = hole' "ctrParamListToNode"

typeArgListToNode :: AboveInfo -> ListTypeArgRecValue -> Node
typeArgListToNode aboveInfo tyArgs = hole' "typeArgListToNode"

constructorListToNode :: AboveInfo -> ListCtrRecValue -> Node
constructorListToNode aboveInfo ctrs = hole' "constructorListToNode"
