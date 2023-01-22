module TypeCraft.Purescript.TermToNode where

import Prelude
import Prim hiding (Type)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Change(..), Constructor, CtrParam, Term(..), TermBind(..), Tooth(..), Type(..), TypeArg, TypeBind(..), UpPath)
import TypeCraft.Purescript.Node (Node, NodeIndentation, NodeTag(..), makeIndentNodeIndentation, makeInlineNodeIndentation, makeNewlineNodeIndentation, makeNode, setCalculatedNodeIsParenthesized, setNodeIndentation, setNodeIsParenthesized, setNodeLabel, termToNodeTag, typeToNodeTag)
import TypeCraft.Purescript.State (CursorLocation(..), Select(..), makeCursorMode, makeSelectMode)
import TypeCraft.Purescript.TermRec (ListCtrParamRecValue, ListTypeArgRecValue, ListTypeBindRecValue, TermBindRecValue, TermRecValue, TypeArgRecValue, TypeBindRecValue, TypeRecValue, ListCtrRecValue, recTerm, recType)
import TypeCraft.Purescript.Util (hole, hole', justWhen)

data AboveInfo syn
  = AICursor UpPath
  | AISelect UpPath AllContext syn UpPath -- top path, then program below, then middle path

stepAI :: forall syn. Tooth -> AboveInfo syn -> AboveInfo syn
stepAI tooth (AICursor path) = AICursor (tooth : path)

stepAI tooth (AISelect topPath ctx term midPath) = AISelect topPath ctx term (tooth : midPath)

aIOnlyCursor :: forall syn1 syn2. AboveInfo syn1 -> AboveInfo syn2
aIOnlyCursor (AICursor path) = AICursor path

aIOnlyCursor (AISelect topPath ctx term midPath) = AICursor (midPath <> topPath)

aIGetPath :: forall syn. AboveInfo syn -> UpPath
aIGetPath (AICursor path) = path

aIGetPath (AISelect top ctx term middle) = middle <> top

newlineIf :: Boolean -> NodeIndentation
newlineIf = if _ then makeNewlineNodeIndentation else makeInlineNodeIndentation

indentIf :: Boolean -> NodeIndentation
indentIf = if _ then makeIndentNodeIndentation else makeInlineNodeIndentation

inline :: NodeIndentation
inline = makeInlineNodeIndentation

-- | PreNode
type PreNode
  = NodeIndentation -> Tooth -> Node

arrangeNodeKids ::
  forall a.
  { isActive :: Boolean
  , aboveInfo :: AboveInfo a
  , tag :: NodeTag
  , stepAIKids :: Array PreNode -> Array Node
  , makeCursor :: Unit -> CursorLocation
  , makeSelect :: UpPath → AllContext → a → UpPath -> Select
  } ->
  Array PreNode ->
  Node
arrangeNodeKids args kids =
  makeNode
    { kids: setCalculatedNodeIsParenthesized args.tag <$> args.stepAIKids kids
    , getCursor: justWhen args.isActive \_ -> _ { mode = makeCursorMode $ args.makeCursor unit }
    , getSelect:
        case args.aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx a midPath -> justWhen args.isActive \_ -> _ { mode = makeSelectMode $ args.makeSelect topPath topCtx a midPath }
    , tag: args.tag
    }

arrangeKid :: forall a rc. AboveInfo a -> (AboveInfo a -> rc -> Node) -> rc -> PreNode
arrangeKid ai k rc ind th = setNodeIndentation ind $ k (stepAI th ai) rc

-- | Term
stepAIKidsTerm :: Term -> Array PreNode -> Array Node
stepAIKidsTerm term kids = case term of
  App md apl arg ty1 ty2
    | [ k_apl, k_arg ] <- kids -> [ k_apl inline (App1 md arg ty1 ty2), k_arg (indentIf md.argIndented) (App1 md apl ty1 ty2) ]
  Lambda md bnd sig body ty
    | [ k_bnd, k_ty, k_body ] <- kids -> [ k_bnd inline (Lambda1 md sig body ty), k_ty (indentIf md.bodyIndented) (Lambda2 md bnd body ty), k_body inline (Lambda3 md bnd sig ty) ]
  Var md x args
    | [] <- kids -> []
  Let md bnd bnds imp sig bod ty
    | [ k_bnd, k_bnds, k_imp, k_sig, k_bod ] <- kids -> [ k_bnd inline (Let1 md bnds imp sig bod ty), k_bnds inline (Let2 md bnd imp sig bod ty), k_imp (indentIf md.defIndented) (Let3 md bnd bnds sig bod ty), k_sig (indentIf md.typeIndented) (Let4 md bnd bnds imp bod ty), k_bod (newlineIf md.bodyIndented) (Let5 md bnd bnds imp sig ty) ]
  Data md bnd bnds ctrs bod ty
    | [ k_bnd, k_bnds, k_ctrs, k_bod ] <- kids -> [ k_bnd inline (Data1 md bnds ctrs bod ty), k_bnds inline (Data2 md bnd ctrs bod ty), k_ctrs inline (Data3 md bnd bnds bod ty), k_bod inline (Data4 md bnd bnds ctrs ty) ]
  TLet md bnd bnds sig bod ty
    | [ k_bnd, k_bnds, k_sig, k_bod ] <- kids -> [ k_bnd inline (TLet1 md bnds sig bod ty), k_bnds inline (TLet2 md bnd sig bod ty), k_sig inline (TLet3 md bnd bnds bod ty), k_bod inline (TLet4 md bnd bnds sig ty) ]
  TypeBoundary md ch bod
    | [ k_bod ] <- kids -> [ k_bod inline (TypeBoundary1 md ch) ]
  ContextBoundary md x ch bod
    | [ k_bod ] <- kids -> [ k_bod inline (ContextBoundary1 md x ch) ]
  Hole md
    | [] <- kids -> []
  Buffer md imp sig bod ty
    | [ k_imp, k_sig, k_bod ] <- kids -> [ k_imp inline (Buffer1 md sig bod ty), k_sig inline (Buffer2 md imp bod ty), k_bod inline (Buffer3 md imp sig ty) ]
  _ -> unsafeThrow "stepAIKidsTerm: malformed input"

arrangeTerm ::
  { isActive :: Boolean
  , aboveInfo :: AboveInfo (Term /\ Type)
  , term :: TermRecValue
  } ->
  Array PreNode ->
  Node
arrangeTerm args =
  arrangeNodeKids
    { isActive: args.isActive
    , aboveInfo: args.aboveInfo
    , tag: termToNodeTag args.term.term
    , stepAIKids: stepAIKidsTerm args.term.term
    , makeCursor: \_ -> TermCursor args.term.ctxs args.term.ty (aIGetPath args.aboveInfo) args.term.term
    , makeSelect: \topPath topCtx (topTerm /\ topTy) midPath -> TermSelect topPath topCtx topTy topTerm midPath args.term.ctxs args.term.ty args.term.term false
    }

--- need to track a path for the cursor, and two paths for the selction. also,
-- might consider deriving the cursor path from those two in that case?
--
-- TODO: put TermPath into TermRecValue, and then don't need the TermPath
-- argument here! Problem: what if I really did just have a term, without a
-- TermPath though? I should still be able to recurse over that. So what is the
-- right design here?
-- 
-- TODO: problem is that it doesn't abstract out metadata properly, so its
-- currently not handling indentation
termToNode :: Boolean -> AboveInfo (Term /\ Type) -> TermRecValue -> Node
termToNode isActive aboveInfo term =
  recTerm
    ( { lambda:
          \md tBind ty body _bodyTy ->
            arrangeTerm args
              [ arrangeKid ai (termBindToNode isActive) tBind
              , arrangeKid ai (typeToNode isActive) ty
              , arrangeKid ai (termToNode isActive) body
              ]
      , app:
          \md t1 t2 _argTy _outTy ->
            arrangeTerm args
              [ arrangeKid ai (termToNode isActive) t1
              , arrangeKid ai (termToNode isActive) t2
              ]
      , var: \md x targs -> arrangeTerm args []
      , lett:
          \md tBind tyBinds def defTy body _bodyTy ->
            arrangeTerm args
              [ arrangeKid ai (termBindToNode isActive) tBind
              , arrangeKid ai (typeBindListToNode isActive) tyBinds
              , arrangeKid ai (termToNode isActive) def
              , arrangeKid ai (typeToNode isActive) defTy
              , arrangeKid ai (termToNode isActive) body
              ]
      , dataa:
          \md x tbinds ctrs body _bodyTy ->
            arrangeTerm args
              [ arrangeKid ai (typeBindToNode isActive) x
              , arrangeKid ai (typeBindListToNode isActive) tbinds
              , arrangeKid ai (constructorListToNode isActive) ctrs
              , arrangeKid ai (termToNode isActive) body
              ]
      , tlet:
          \md tyBind tyBinds def body _bodyTy ->
            arrangeTerm args
              [ arrangeKid ai (typeBindToNode isActive) tyBind
              , arrangeKid ai (typeBindListToNode isActive) tyBinds
              , arrangeKid ai (typeToNode isActive) def
              , arrangeKid ai (termToNode isActive) body
              ]
      , typeBoundary:
          \md ch t ->
            arrangeTerm args
              [ arrangeKid ai (termToNode isActive) t
              , arrangeKid ai (const changeToNode) { ch, ctxs: term.ctxs }
              ]
      , contextBoundary:
          \md x c t ->
            arrangeTerm args
              [ arrangeKid ai (termToNode isActive) t
              ]
      , hole: \md -> arrangeTerm args []
      , buffer:
          \md def defTy body _bodyTy ->
            arrangeTerm args
              [ arrangeKid ai (termToNode isActive) def
              , arrangeKid ai (typeToNode isActive) defTy
              , arrangeKid ai (termToNode isActive) body
              ]
      }
    )
    term
  where
  args = { isActive, aboveInfo, term }

  ai :: forall a. AboveInfo a
  ai = aIOnlyCursor aboveInfo

-- | Type
stepAIKidsType :: Type -> Array PreNode -> Array Node
stepAIKidsType ty kids = case ty of
  Arrow md ty1 ty2 -> hole
  TNeu md id args -> hole
  THole md id -> hole

arrangeType ::
  { isActive :: Boolean
  , aboveInfo :: AboveInfo Type
  , ty :: TypeRecValue
  } ->
  Array PreNode ->
  Node
arrangeType args =
  arrangeNodeKids
    { isActive: args.isActive
    , aboveInfo: args.aboveInfo
    , tag: typeToNodeTag args.ty.ty
    , stepAIKids: stepAIKidsType args.ty.ty
    , makeCursor: \_ -> TypeCursor args.ty.ctxs (aIGetPath args.aboveInfo) args.ty.ty
    , makeSelect: \topPath topCtx topTy midPath -> TypeSelect topPath topCtx topTy midPath args.ty.ctxs args.ty.ty false
    }

typeToNode :: Boolean -> AboveInfo Type -> TypeRecValue -> Node
typeToNode isActive aboveInfo ty =
  recType
    { arrow:
        \md ty1 ty2 ->
          arrangeType args
            [ arrangeKid ai (typeToNode isActive) ty1
            , arrangeKid ai (typeToNode isActive) ty2
            ]
    , tNeu:
        \md x tyArgs ->
          arrangeType args
            [ arrangeKid ai (typeArgListToNode isActive) tyArgs
            ]
    , tHole: \md x -> arrangeType args []
    }
    ty
  where
  args = { isActive, aboveInfo, ty }

  ai :: forall a. AboveInfo a
  ai = aIOnlyCursor aboveInfo

-- | ListCtr
ctrListToNode :: Boolean -> AboveInfo Constructor -> ListCtrRecValue -> Node
ctrListToNode isActive aboveInfo ctrs = hole' "ctrListToNode"

-- | Ctr
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
-- | TypeArg
typeArgToNode :: Boolean -> AboveInfo TypeArg -> TypeArgRecValue -> Node
typeArgToNode isActive aboveInfo tyArg = hole' "typeArgToNode"

-- TypeBind
typeBindToNode :: Boolean -> AboveInfo TypeBind -> TypeBindRecValue -> Node
typeBindToNode isActive aboveInfo { ctxs, tyBind: tyBind@(TypeBind md x) } =
  setNodeLabel md.varName
    $ makeNode
        { kids: []
        , getCursor:
            justWhen isActive \_ -> _ { mode = makeCursorMode $ TypeBindCursor ctxs (aIGetPath aboveInfo) tyBind }
        , getSelect: Nothing
        , tag: TypeBindNodeTag
        }

-- TypeBind
typeBindListToNode :: Boolean -> AboveInfo (List TypeBind) -> ListTypeBindRecValue -> Node
typeBindListToNode isActive aboveInfo tyBinds =  -- TODO: write actual implementation
  makeNode
    { tag: TypeBindListNilNodeTag
    , kids: []
    , getCursor: justWhen isActive \_ -> _ { mode = makeCursorMode $ TypeBindListCursor tyBinds.ctxs (aIGetPath aboveInfo) tyBinds.tyBinds }
    , getSelect: Nothing
    }

-- TermBind
termBindToNode :: Boolean -> AboveInfo TermBind -> TermBindRecValue -> Node
termBindToNode isActive aboveInfo { ctxs, tBind: tBind@(TermBind md x) } =
  setNodeLabel md.varName
    $ makeNode
        { kids: []
        , getCursor:
            justWhen isActive \_ -> _ { mode = makeCursorMode $ TermBindCursor ctxs (aIGetPath aboveInfo) tBind }
        , getSelect: Nothing
        , tag: TermBindNodeTag
        }

-- CtrParamList
ctrParamListToNode :: Boolean -> AboveInfo (List CtrParam) -> ListCtrParamRecValue -> Node
ctrParamListToNode isActive aboveInfo ctrParams = hole' "ctrParamListToNode"

-- ArgParamList
typeArgListToNode :: Boolean -> AboveInfo (List TypeArg) -> ListTypeArgRecValue -> Node
typeArgListToNode isActive aboveInfo tyArgs = hole' "typeArgListToNode"

-- ConstructorList
constructorListToNode :: Boolean -> AboveInfo (List Constructor) -> ListCtrRecValue -> Node
constructorListToNode isActive aboveInfo ctrs =  -- TODO: This is just a placeholder implementation of this function
  makeNode
    { tag: ConstructorListNilNodeTag
    , kids: []
    , getCursor: justWhen isActive \_ -> _ { mode = makeCursorMode $ CtrListCursor ctrs.ctxs (aIGetPath aboveInfo) ctrs.ctrs }
    , getSelect: Nothing
    }

-- | Change
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
    setNodeIsParenthesized true
      $ makeChangeNode
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
