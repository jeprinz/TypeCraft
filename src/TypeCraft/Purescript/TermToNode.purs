module TypeCraft.Purescript.TermToNode where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar

import Data.List (List(..), (:))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe', maybe')
import Debug (trace)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Node (Node, NodeTag(..), makeNode, setCalculatedNodeData, setNodeIndentation, setNodeLabel, setNodeLabelMaybe, setNodeParenthesized)
import TypeCraft.Purescript.Node (makeIndentNodeIndentation)
import TypeCraft.Purescript.Node (setNodeIndentation)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode, makeState)
import TypeCraft.Purescript.TermRec (ListCtrParamRecValue, ListTypeArgRecValue, ListTypeBindRecValue, TermBindRecValue, TermRecValue, TypeArgRecValue, TypeBindRecValue, TypeRecValue, ListCtrRecValue, recTerm, recType)
import TypeCraft.Purescript.Util (hole', justWhen)

data AboveInfo syn
  = AICursor UpPath
  | AISelect UpPath AllContext syn UpPath -- top path, then program below, then middle path

stepAI :: forall syn. Tooth -> AboveInfo syn -> AboveInfo syn
stepAI tooth (AICursor path) = AICursor (tooth : path)

stepAI tooth (AISelect topPath ctx term middlePath) = AISelect topPath ctx term (tooth : middlePath)

aIOnlyCursor :: forall syn1 syn2. AboveInfo syn1 -> AboveInfo syn2
aIOnlyCursor (AICursor path) = AICursor path

aIOnlyCursor (AISelect topPath ctx term middlePath) = AICursor (middlePath <> topPath)

aIGetPath :: forall syn. AboveInfo syn -> UpPath
aIGetPath (AICursor path) = path

aIGetPath (AISelect top ctx term middle) = middle <> top

indentIf :: Boolean -> Node -> Node
indentIf false n = n

indentIf true n = setNodeIndentation makeIndentNodeIndentation n

-- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?
-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: Boolean -> AboveInfo (Term /\ Type) -> TermRecValue -> Node
termToNode isActive aboveInfo term =
  let
    nodeInfo =
      recTerm
        ( { lambda:
              \md tBind ty body bodyTy ->
                { tag: LambdaNodeTag
                , label: Nothing
                , kids:
                    [ termBindToNode isActive (stepAI (Lambda1 md ty.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tBind
                    , typeToNode isActive (stepAI (Lambda2 md tBind.tBind body.term bodyTy) (aIOnlyCursor aboveInfo)) ty
                    , termToNode isActive (stepAI (Lambda3 md tBind.tBind ty.ty bodyTy) aboveInfo) body
                    ]
                }
          , app:
              \md t1 t2 argTy outTy ->
                { tag: AppNodeTag
                , label: Nothing
                , kids:
                    [ termToNode isActive (stepAI (App1 md t2.term argTy outTy) aboveInfo) t1
                    , termToNode isActive (stepAI (App2 md t1.term argTy outTy) aboveInfo) t2
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
                    [ termBindToNode isActive (stepAI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tBind
                    , typeBindListToNode isActive (stepAI (Let2 md tBind.tBind {-List TypeBind-} def.term defTy.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tyBinds
                    , typeToNode isActive (stepAI (Let4 md tBind.tBind tyBinds.tyBinds def.term body.term bodyTy) (aIOnlyCursor aboveInfo)) defTy
                    , termToNode isActive (stepAI (Let3 md tBind.tBind tyBinds.tyBinds defTy.ty body.term bodyTy) aboveInfo) def
                    , indentIf md.bodyIndented $ termToNode isActive (stepAI (Let5 md tBind.tBind tyBinds.tyBinds def.term defTy.ty bodyTy) aboveInfo) body
                    ]
                }
          , dataa:
              \md x tbinds ctrs body bodyTy ->
                { tag: DataNodeTag
                , label: Nothing
                , kids:
                    [ typeBindToNode isActive (stepAI (Data1 md tbinds.tyBinds ctrs.ctrs term.term bodyTy) (aIOnlyCursor aboveInfo)) x
                    , typeBindListToNode isActive (stepAI (Data2 md x.tyBind ctrs.ctrs term.term bodyTy) (aIOnlyCursor aboveInfo)) tbinds
                    , constructorListToNode isActive (stepAI (Data3 md x.tyBind tbinds.tyBinds term.term bodyTy) (aIOnlyCursor aboveInfo)) ctrs
                    , termToNode isActive (stepAI (Data4 md x.tyBind tbinds.tyBinds ctrs.ctrs bodyTy) aboveInfo) body
                    ]
                }
          , tlet: \md x tbinds def body bodyTy -> hole' "termToNode"
          , typeBoundary:
              \md ch t ->
                { tag: TypeBoundaryNodeTag
                , label: Nothing
                , kids:
                    [ termToNode isActive (stepAI (TypeBoundary1 md ch) aboveInfo) t
                    , changeToNode { ch, ctxs: term.ctxs }
                    ]
                }
          , contextBoundary:
              \md x c t ->
                { tag: ContextBoundaryNodeTag
                , label: Nothing
                , kids: [ termToNode isActive (stepAI (ContextBoundary1 md x c) aboveInfo) t ]
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
                    [ termToNode isActive (stepAI (Buffer1 md defTy.ty body.term bodyTy) aboveInfo) def
                    , typeToNode isActive (stepAI (Buffer2 md def.term body.term bodyTy) (aIOnlyCursor aboveInfo)) defTy
                    , termToNode isActive (stepAI (Buffer3 md def.term defTy.ty bodyTy) aboveInfo) body
                    ]
                }
          }
        )
        term
  in
    -- pieces that are the same for every syntactic form are done here:
    setNodeLabelMaybe nodeInfo.label
      $ makeNode
          { kids: setCalculatedNodeData nodeInfo.tag <$> nodeInfo.kids
          , getCursor:
              justWhen isActive \_ _ ->
                makeState $ makeCursorMode $ TermCursor term.ctxs term.ty (aIGetPath aboveInfo) term.term
          , getSelect:
              case aboveInfo of
                AICursor _path -> Nothing
                AISelect topPath topCtx (topTerm /\ topTy) middlePath ->
                  justWhen isActive \_ _ ->
                    makeState $ SelectMode
                      $ { select: TermSelect topPath topCtx topTy topTerm middlePath term.ctxs term.ty term.term false }
          , tag: nodeInfo.tag
          }

typeToNode :: Boolean -> AboveInfo Type -> TypeRecValue -> Node
typeToNode isActive aboveInfo ty =
  let
    nodeInfo =
      recType
        ( { arrow:
              \md ty1 ty2 ->
                { tag: ArrowNodeTag
                , kids:
                    [ typeToNode isActive (stepAI (Arrow1 md ty2.ty) aboveInfo) ty1
                    , typeToNode isActive (stepAI (Arrow2 md ty1.ty) aboveInfo) ty2
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
      { kids: nodeInfo.kids
      , getCursor:
          justWhen isActive \_ _ ->
            makeState $ makeCursorMode $ TypeCursor ty.ctxs (aIGetPath aboveInfo) ty.ty
      , getSelect:
          case aboveInfo of
            AICursor path -> Nothing -- TODO: impl select
            AISelect topPath topCtx topTy middlePath ->
              justWhen isActive \_ _ ->
                makeState $ SelectMode
                  $ { select: TypeSelect topPath topCtx topTy middlePath ty.ctxs ty.ty false }
      , tag: nodeInfo.tag
      }

ctrListToNode :: Boolean -> AboveInfo Constructor -> ListCtrRecValue -> Node
ctrListToNode isActive aboveInfo ctrs = hole' "ctrListToNode"

ctrToNode :: Boolean -> AboveInfo Constructor -> Constructor -> Node
ctrToNode isActive aboveInfo ctr = hole' "ctrToNode"

--ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
--ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
--    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
--    , kids: [[typeToNode isActive (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
--    , getCursor: Nothing
--    , getSelect: Nothing
--    , style: makeNormalNodeStyle
--}
typeArgToNode :: Boolean -> AboveInfo TypeArg -> TypeArgRecValue -> Node
typeArgToNode isActive aboveInfo tyArg = hole' "typeArgToNode"

typeBindToNode :: Boolean -> AboveInfo TypeBind -> TypeBindRecValue -> Node
typeBindToNode isActive aboveInfo tyBind = hole' "typeBindToNode"

typeBindListToNode :: Boolean -> AboveInfo (List TypeBind) -> ListTypeBindRecValue -> Node
typeBindListToNode isActive aboveInfo tyBinds =  -- TODO: write actual implementation
  makeNode
    { tag: TypeBindListNilNodeTag
    , kids: []
    , getCursor: justWhen isActive \_ _ -> makeState $ makeCursorMode $ TypeBindListCursor tyBinds.ctxs (aIGetPath aboveInfo) tyBinds.tyBinds
    , getSelect: Nothing
    }

termBindToNode :: Boolean -> AboveInfo TermBind -> TermBindRecValue -> Node
termBindToNode isActive aboveInfo { ctxs, tBind: tBind@(TermBind md x) } =
  setNodeLabel md.varName
    $ makeNode
        { kids: []
        , getCursor:
            justWhen isActive \_ _ ->
              makeState $ makeCursorMode $ TermBindCursor ctxs (aIGetPath aboveInfo) tBind
        , getSelect: Nothing
        , tag: TermBindNodeTag
        }

ctrParamListToNode :: Boolean -> AboveInfo (List CtrParam) -> ListCtrParamRecValue -> Node
ctrParamListToNode isActive aboveInfo ctrParams = hole' "ctrParamListToNode"

typeArgListToNode :: Boolean -> AboveInfo (List TypeArg) -> ListTypeArgRecValue -> Node
typeArgListToNode isActive aboveInfo tyArgs = hole' "typeArgListToNode"

constructorListToNode :: Boolean -> AboveInfo (List Constructor) -> ListCtrRecValue -> Node
constructorListToNode isActive aboveInfo ctrs = hole' "constructorListToNode"

type ChangeRecValue
  = { ctxs :: AllContext, ch :: Change }

makeChangeNode :: { kids :: Array Node, tag :: NodeTag } -> Node
makeChangeNode { tag, kids } = makeNode { tag, kids, getCursor: Nothing, getSelect: Nothing }

changeToNode :: ChangeRecValue -> Node
changeToNode val = case val.ch of
  CArrow ch1 ch2 ->
    makeChangeNode
      { tag: ArrowNodeTag
      , kids:
          [ changeToNode val { ch = ch1 }
          , changeToNode val { ch = ch2 }
          ]
      }
  CHole _ ->
    makeChangeNode
      { tag: THoleNodeTag
      , kids: []
      }
  Replace ty1 ty2 ->
    setNodeParenthesized true $
    makeChangeNode
      { tag: ReplaceNodeTag
      , kids:
          [ typeToNode false dummyAboveInfo { ctxs: val.ctxs, ty: ty1 }
          , typeToNode false dummyAboveInfo { ctxs: val.ctxs, ty: ty2 }
          ]
      }
  Plus ty ch ->
    makeChangeNode
      { tag: PlusNodeTag
      , kids:
          [ typeToNode false dummyAboveInfo { ctxs: val.ctxs, ty }
          , changeToNode val { ch = ch }
          ]
      }
  Minus ty ch ->
    makeChangeNode
      { tag: MinusNodeTag
      , kids:
          [ typeToNode false dummyAboveInfo { ctxs: val.ctxs, ty }
          , changeToNode val { ch = ch }
          ]
      }
  CNeu id args ->
    makeChangeNode
      { tag: TNeuNodeTag
      , kids: [] -- TODO: type args 
      }

-- since this will never be used for non-cursorable things
-- TODO: make AboveInfo a Maybe, so that when its nothing covers the false
-- Boolean case in *toNode functions
dummyAboveInfo :: forall a. AboveInfo a
dummyAboveInfo = AICursor Nil
