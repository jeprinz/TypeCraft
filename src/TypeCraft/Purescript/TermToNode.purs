module TypeCraft.Purescript.TermToNode where

import Prelude
import Prim hiding (Type)
import Data.Array as Array
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Change(..), Constructor, CtrParam, Term(..), TermBind(..), Tooth(..), Type(..), TypeArg, TypeBind(..), UpPath)
import TypeCraft.Purescript.Node (Node, NodeIndentation, NodeTag(..), getNodeTag, makeIndentNodeIndentation, makeInlineNodeIndentation, makeNewlineNodeIndentation, makeNode, setNodeIndentation, setNodeIsParenthesized, setNodeLabel, termToNodeTag, typeToNodeTag)
import TypeCraft.Purescript.State (CursorLocation(..), Select(..), makeCursorMode, makeSelectMode)
import TypeCraft.Purescript.TermRec (ListCtrParamRecValue, ListCtrRecValue, ListTypeArgRecValue, ListTypeBindRecValue, TermBindRecValue, TermRecValue, TypeArgRecValue, TypeBindRecValue, TypeRecValue, CtrParamRecValue, recTerm, recType)
import TypeCraft.Purescript.Util (hole', justWhen, lookup')

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

type PreNode
  = Tooth -> Node

arrangeNodeKids ::
  { isActive :: Boolean
  , tag :: NodeTag
  , makeCursor :: Unit -> Maybe CursorLocation
  , makeSelect :: Unit -> Maybe Select
  , stepKids :: Array PreNode -> Array Node
  } ->
  Array PreNode ->
  Node
arrangeNodeKids args kids =
  makeNode
    { kids: args.stepKids kids
    , getCursor:
        join
          $ justWhen args.isActive \_ -> do
              cursorLocation <- args.makeCursor unit
              Just (_ { mode = makeCursorMode cursorLocation })
    , getSelect:
        join
          $ justWhen args.isActive \_ -> do
              select <- args.makeSelect unit
              Just (_ { mode = makeSelectMode select })
    , tag: args.tag
    }

arrangeKidAI :: forall a recVal. AboveInfo a -> (AboveInfo a -> recVal -> Node) -> recVal -> PreNode
arrangeKidAI info k rv th = k (stepAI th info) rv

-- ** Term
-- | here is where indentation and parenthesization happens
stepKidsTerm :: Term -> Array PreNode -> Array Node
stepKidsTerm term kids = case term of
  App md apl arg ty1 ty2
    | [ k_apl, k_arg ] <- kids ->
      [ k_apl (App1 md arg ty1 ty2)
      , setNodeIndentation (indentIf md.argIndented) $ k_arg (App1 md apl ty1 ty2)
      ]
  Lambda md bnd sig body ty
    | [ k_bnd, k_ty, k_body ] <- kids ->
      [ k_bnd (Lambda1 md sig body ty)
      , k_ty (Lambda2 md bnd body ty)
      , setNodeIndentation (indentIf md.bodyIndented) $ k_body (Lambda3 md bnd sig ty)
      ]
  Var md x args
    | [] <- kids -> []
  Let md bnd bnds imp sig bod ty
    | [ k_bnd, k_bnds, k_sig, k_imp, k_bod ] <- kids ->
      [ k_bnd (Let1 md bnds imp sig bod ty)
      , k_bnds (Let2 md bnd imp sig bod ty)
      , setNodeIndentation (indentIf md.typeIndented) $ k_sig (Let4 md bnd bnds imp bod ty) -- NOTE: Yes, these are out of order. Yes, they need to stay like that.
      , setNodeIndentation (indentIf md.defIndented) $ k_imp (Let3 md bnd bnds sig bod ty)
      , setNodeIndentation (newlineIf md.bodyIndented) $ k_bod (Let5 md bnd bnds imp sig ty)
      ]
  Data md bnd bnds ctrs bod ty
    | [ k_bnd, k_bnds, k_ctrs, k_bod ] <- kids ->
      [ k_bnd (Data1 md bnds ctrs bod ty)
      , k_bnds (Data2 md bnd ctrs bod ty)
      , k_ctrs (Data3 md bnd bnds bod ty)
      , k_bod (Data4 md bnd bnds ctrs ty)
      ]
  TLet md bnd bnds sig bod ty
    | [ k_bnd, k_bnds, k_sig, k_bod ] <- kids ->
      [ k_bnd (TLet1 md bnds sig bod ty)
      , k_bnds (TLet2 md bnd sig bod ty)
      , k_sig (TLet3 md bnd bnds bod ty)
      , k_bod (TLet4 md bnd bnds sig ty)
      ]
  TypeBoundary md ch bod
    | [ k_bod ] <- kids -> [ k_bod (TypeBoundary1 md ch) ]
  ContextBoundary md x ch bod
    | [ k_bod ] <- kids -> [ k_bod (ContextBoundary1 md x ch) ]
  Hole md
    | [] <- kids -> []
  Buffer md imp sig bod ty
    | [ k_imp, k_sig, k_bod ] <- kids ->
      [ k_imp (Buffer1 md sig bod ty)
      , k_sig (Buffer2 md imp bod ty)
      , k_bod (Buffer3 md imp sig ty)
      ]
  _ -> unsafeThrow $ "stepKidsTerm: wrong number of kids\nterm = " <> show term <> "\nlength kids = " <> show (Array.length kids)

type TermNodeCursorInfo =
  { isActive :: Boolean
  , makeCursor :: Unit -> Maybe CursorLocation
  , makeSelect :: Unit -> Maybe Select
  , term :: TermRecValue
  }
arrangeTerm ::
  TermNodeCursorInfo ->
  Array PreNode ->
  Node
arrangeTerm args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: termToNodeTag args.term.term
    , stepKids: stepKidsTerm args.term.term
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
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
    { lambda:
        \md tBind ty body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI ai (termBindToNode isActive) tBind
            , arrangeKidAI ai (typeToNode isActive) ty
            , arrangeKidAI ai (termToNode isActive) body
            ]
    , app:
        \md t1 t2 _argTy _outTy ->
          arrangeTerm args
            [ arrangeKidAI ai (termToNode isActive) t1
            , arrangeKidAI ai (termToNode isActive) t2
            ]
    , var: \md x targs -> setNodeLabel (x `lookup'` term.ctxs.mdctx) $ arrangeTerm args []
    , lett:
        \md tBind tyBinds def defTy body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI ai (termBindToNode isActive) tBind
            , arrangeKidAI ai (typeBindListToNode isActive) tyBinds
            , arrangeKidAI ai (typeToNode isActive) defTy
            , arrangeKidAI ai (termToNode isActive) def
            , arrangeKidAI ai (termToNode isActive) body
            ]
    , dataa:
        \md x tbinds ctrs body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI ai (typeBindToNode isActive) x
            , arrangeKidAI ai (typeBindListToNode isActive) tbinds
            , arrangeKidAI ai (ctrListToNode isActive) ctrs
            , arrangeKidAI ai (termToNode isActive) body
            ]
    , tlet:
        \md tyBind tyBinds def body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI ai (typeBindToNode isActive) tyBind
            , arrangeKidAI ai (typeBindListToNode isActive) tyBinds
            , arrangeKidAI ai (typeToNode isActive) def
            , arrangeKidAI ai (termToNode isActive) body
            ]
    , typeBoundary:
        \md ch t ->
          arrangeTerm args
            [ arrangeKidAI ai (termToNode isActive) t
            , arrangeKidAI ai (const changeToNode) { ch, ctxs: term.ctxs }
            ]
    , contextBoundary:
        \md x c t ->
          arrangeTerm args
            [ arrangeKidAI ai (termToNode isActive) t
            ]
    , hole: \md -> arrangeTerm args []
    , buffer:
        \md def defTy body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI ai (termToNode isActive) def
            , arrangeKidAI ai (typeToNode isActive) defTy
            , arrangeKidAI ai (termToNode isActive) body
            ]
    }
    term
  where
  args =
    { isActive
    , makeCursor: \_ -> Just $ TermCursor term.ctxs term.ty (aIGetPath aboveInfo) term.term
    , makeSelect:
        \_ -> case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx (topTerm /\ topTy) midPath -> Just $ TermSelect topPath topCtx topTy topTerm midPath args.term.ctxs args.term.ty args.term.term false
    , term
    }

  ai :: forall a. AboveInfo a
  ai = aIOnlyCursor aboveInfo

-- ** Type
-- | here is where indentation and parenthesization happens
stepKidsType :: Type -> Array PreNode -> Array Node
stepKidsType ty kids = case ty of
  Arrow md ty1 ty2
    | [ k_ty1, k_ty2 ] <- kids ->
      [ let node = k_ty1 (Arrow1 md ty2) in setNodeIsParenthesized (getNodeTag node == ArrowNodeTag) node
      , setNodeIndentation (indentIf md.codIndented) $ k_ty2 (Arrow2 md ty1)
      ]
  TNeu md x args
    | [ k_args ] <- kids -> [ k_args (TNeu1 md x) ]
  THole md id
    | [] <- kids -> []
  _ -> unsafeThrow "stepKidsType: wrong number of kids"

type TypeNodeCursorInfo =
  { isActive :: Boolean
  , ty :: TypeRecValue
  , makeCursor :: Unit -> Maybe CursorLocation
  , makeSelect :: Unit -> Maybe Select
  }
arrangeType ::
  TypeNodeCursorInfo ->
  Array PreNode ->
  Node
arrangeType args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: typeToNodeTag args.ty.ty
    , stepKids: stepKidsType args.ty.ty
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

typeToNode :: Boolean -> AboveInfo Type -> TypeRecValue -> Node
typeToNode isActive aboveInfo ty =
  recType
    { arrow:
        \md ty1 ty2 ->
          arrangeType args
            [ arrangeKidAI ai (typeToNode isActive) ty1
            , arrangeKidAI ai (typeToNode isActive) ty2
            ]
    , tNeu:
        \md x tyArgs ->
          arrangeType args
            [ arrangeKidAI ai (typeArgListToNode isActive) tyArgs
            ]
    , tHole: \md x -> arrangeType args []
    }
    ty
  where
  args =
    { isActive
    , makeCursor: \_ -> Just $ TypeCursor args.ty.ctxs (aIGetPath aboveInfo) ty.ty
    , makeSelect:
        \_ -> case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx topTy midPath -> Just $ TypeSelect topPath topCtx topTy midPath ty.ctxs ty.ty false
    , ty
    }

  ai :: forall a. AboveInfo a
  ai = aIOnlyCursor aboveInfo

-- Constructor
ctrToNode :: Boolean -> AboveInfo Constructor -> Constructor -> Node
ctrToNode isActive aboveInfo ctr = hole' "ctrToNode"

-- CtrParam
--
--ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
--ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
--    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
--    , kids: [[typeToNode isActive (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
--    , getCursor: Nothing
--    , getSelect: Nothing
--    , style: makeNormalNodeStyle
arrangeCtrParam :: { isActive :: Boolean, aboveInfo :: AboveInfo CtrParam, ctrParam :: CtrParamRecValue } -> Array PreNode -> Node
arrangeCtrParam = hole' "arrangeCtrParam"

ctrParamToNode :: Boolean -> AboveInfo CtrParam -> CtrParam -> Node
ctrParamToNode = hole' "ctrParamToNode"

-- TypeArg
arrangeTypeArg :: { isActive :: Boolean, aboveInfo :: AboveInfo TypeArg, tyArg :: TypeArgRecValue } -> Array PreNode -> Node
arrangeTypeArg = hole' "arrangeTypeArg"

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
ctrListToNode :: Boolean -> AboveInfo (List Constructor) -> ListCtrRecValue -> Node
ctrListToNode isActive aboveInfo ctrs =  -- TODO: This is just a placeholder implementation of this function
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
