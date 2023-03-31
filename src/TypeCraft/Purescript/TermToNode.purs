module TypeCraft.Purescript.TermToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec
import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID as UUID
import Debug (trace, traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context (AllContext, typeVarGetName)
import TypeCraft.Purescript.CursorMovement (getMiddlePath)
import TypeCraft.Purescript.Grammar (CTypeVar(..), Change(..), Constructor(..), CtrParam(..), SubChange(..), Term(..), TermBind(..), Tooth(..), Type(..), TypeArg(..), TypeBind(..), TypeVar(..), TypeVarID(..), UpPath)
import TypeCraft.Purescript.MD (defaultTHoleMD)
import TypeCraft.Purescript.Util (justWhen, lookup')

data AboveInfo syn
  = AICursor UpPath
  | AISelect UpPath AllContext syn UpPath -- top path, then program below, then middle path
  | AINothing

stepAI :: forall syn. Tooth -> AboveInfo syn -> AboveInfo syn
stepAI tooth (AICursor path) = AICursor (tooth : path)

stepAI tooth (AISelect topPath ctx term midPath) = AISelect topPath ctx term (tooth : midPath)

stepAI tooth AINothing = AINothing

aIOnlyCursor :: forall syn1 syn2. AboveInfo syn1 -> AboveInfo syn2
aIOnlyCursor (AICursor path) = AICursor path

aIOnlyCursor (AISelect topPath ctx term midPath) = AICursor (midPath <> topPath)

aIOnlyCursor AINothing = AINothing

aIGetPath :: forall syn. AboveInfo syn -> UpPath
aIGetPath (AICursor path) = path

aIGetPath (AISelect top ctx term middle) = middle <> top

aIGetPath AINothing = unsafeThrow "aIGetPath AINothing"

-- don't indent inactive things (such as appear in query previews)
newlineIf :: Boolean -> Boolean -> NodeIndentation
newlineIf _isActive isNewlined = if isNewlined then makeNewlineNodeIndentation else makeInlineNodeIndentation

-- don't indent inactive things (such as appear in query previews)
indentIf :: Boolean -> Boolean -> NodeIndentation
indentIf _isActive isIndented = if isIndented then makeIndentNodeIndentation else makeInlineNodeIndentation

inline :: NodeIndentation
inline = makeInlineNodeIndentation

type PreNode
  = Tooth -> Node

arrangeNodeKids ::
  { isActive :: Boolean
  , tag :: NodeTag
  , makeCursor :: Maybe CursorLocation
  , makeSelect :: Maybe Select
  , stepKids :: Array PreNode -> Array Node
  } ->
  Array PreNode ->
  Node
arrangeNodeKids args kids =
  let
    getCursor =
      join
        $ justWhen args.isActive \_ -> do
--            traceM "getCursor [purs]"
            cursorLocation <- args.makeCursor
            Just (_ { mode = makeCursorMode cursorLocation })
  in
    makeNode
      { kids: args.stepKids kids
      , getCursor: getCursor
      , getSelect:
          join
            $ justWhen args.isActive \_ -> do
                select <- args.makeSelect
                if List.null (getMiddlePath select) then
                  getCursor
                else
                  Just (_ { mode = makeSelectMode select })
      , tag: args.tag
      }

arrangeKidAI :: forall a recVal. AboveInfo a -> (AboveInfo a -> recVal -> Node) -> recVal -> PreNode
arrangeKidAI info k rv th = k (stepAI th info) rv

modifyNodeIsParenthesized :: (Node -> Boolean) -> Node -> Node
modifyNodeIsParenthesized f n = setNodeIsParenthesized (f n) n

-- ** Term
-- | here is where indentation and parenthesization happens
stepKidsTerm :: Boolean -> Term -> Array PreNode -> Array Node
stepKidsTerm isActive term kids = case term of
  App md apl arg ty1 ty2
    | [ k_apl, k_arg ] <- kids ->
      [ modifyNodeIsParenthesized (not <<< (_ `Array.elem` [ VarNodeTag, AppNodeTag, HoleNodeTag ]) <<< getNodeTag) $ k_apl (App1 md arg ty1 ty2)
      , setNodeIndentation (indentIf isActive md.argIndented) $ modifyNodeIsParenthesized (not <<< (_ `Array.elem` [ VarNodeTag, HoleNodeTag ]) <<< getNodeTag) $ k_arg (App2 md apl ty1 ty2)
      ]
  Lambda md bnd sig body ty
    | [ k_bnd, k_ty, k_body ] <- kids ->
      [ k_bnd (Lambda1 md sig body ty)
      , k_ty (Lambda2 md bnd body ty)
      , setNodeIndentation (indentIf isActive md.bodyIndented) $ k_body (Lambda3 md bnd sig ty)
      ]
  Var md x args
    | [ k_tyargs ] <- kids -> [ addNodeStyle (NodeStyle "list-head-var") $ k_tyargs (Var1 md x {-args-}) ]
  Let md bnd bnds imp sig bod ty
    | [ k_bnd, k_bnds, k_sig, k_imp, k_bod ] <- kids ->
      [ k_bnd (Let1 md bnds imp sig bod ty)
      , addNodeStyle (NodeStyle "list-head") $ k_bnds (Let2 md bnd imp sig bod ty)
      , setNodeIndentation (indentIf isActive md.typeIndented) $ k_sig (Let4 md bnd bnds imp bod ty) -- NOTE: Yes, these are out of order. Yes, they need to stay like that.
      , setNodeIndentation (indentIf isActive md.defIndented) $ k_imp (Let3 md bnd bnds sig bod ty)
      , setNodeIndentation (newlineIf isActive md.bodyIndented) $ k_bod (Let5 md bnd bnds imp sig ty)
      ]
  Data md bnd bnds ctrs bod ty
    | [ k_bnd, k_bnds, k_ctrs, k_bod ] <- kids ->
      [ setNodeIndentation (indentIf isActive md.varIndented) $ k_bnd (Data1 md bnds ctrs bod ty)
      , addNodeStyle (NodeStyle "list-head") $ k_bnds (Data2 md bnd ctrs bod ty)
      , addNodeStyle (NodeStyle "list-head") $ k_ctrs (Data3 md bnd bnds bod ty)
      , setNodeIndentation (newlineIf isActive md.bodyIndented) $ k_bod (Data4 md bnd bnds ctrs ty)
      ]
  TLet md bnd bnds sig bod ty
    | [ k_bnd, k_bnds, k_sig, k_bod ] <- kids ->
      [ k_bnd (TLet1 md bnds sig bod ty)
      , addNodeStyle (NodeStyle "list-head") $ k_bnds (TLet2 md bnd sig bod ty)
      , k_sig (TLet3 md bnd bnds bod ty)
      , k_bod (TLet4 md bnd bnds sig ty)
      ]
  TypeBoundary md ch bod
    | [ k_bod, k_ch ] <- kids -> [ k_bod (TypeBoundary1 md ch), k_ch (TypeBoundary1 md ch) {-TODO: This is a dummy tooth because the change isn't a real node-} ]
  ContextBoundary md x ch bod
    | [ k_bod ] <- kids -> [ k_bod (ContextBoundary1 md x ch) ]
  Hole md
    | [] <- kids -> [] -- the old case
    | [ k_inner ] <- kids -> [ k_inner (Hole1 md) ]
  Buffer md imp sig bod ty
    | [ k_imp, k_sig, k_bod ] <- kids ->
      [ k_imp (Buffer1 md sig bod ty)
      , k_sig (Buffer2 md imp bod ty)
      , k_bod (Buffer3 md imp sig ty)
      ]
  _ -> unsafeThrow $ "stepKidsTerm: wrong number of kids\nterm = " <> show term <> "\nlength kids = " <> show (Array.length kids)

type TermNodeCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
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
    , stepKids: stepKidsTerm args.isActive args.term.term
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
            [ arrangeKidAI cursorOnlyInfo (termBindToNode isActive) tBind
            , arrangeKidAI cursorOnlyInfo (typeToNode isActive) ty
            , arrangeKidAI aboveInfo (termToNode isActive) body
            ]
    , app:
        \md t1 t2 _argTy _outTy ->
          arrangeTerm args
            [ arrangeKidAI aboveInfo (termToNode isActive) t1
            , arrangeKidAI aboveInfo (termToNode isActive) t2
            ]
    , var:
        \md x targs ->
          setNodeMetadata (makeVarNodeMetadata (x `lookup'` term.ctxs.mdctx))
            $ arrangeTerm args
                [ arrangeKidAI cursorOnlyInfo (typeArgListToNode isActive) targs
                ] -- TODO: needs to have type arguments
    , lett:
        \md tBind tyBinds def defTy body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI cursorOnlyInfo (termBindToNode isActive) tBind
            , (\k t -> addNodeStyle (NodeStyle "list-top") (k t)) $ arrangeKidAI cursorOnlyInfo (typeBindListToNode isActive) tyBinds
            , arrangeKidAI cursorOnlyInfo (typeToNode isActive) defTy
            , arrangeKidAI aboveInfo (termToNode isActive) def
            , arrangeKidAI aboveInfo (termToNode isActive) body
            ]
    , dataa:
        \md x tbinds ctrs body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI cursorOnlyInfo (typeBindToNode isActive) x
            , arrangeKidAI cursorOnlyInfo (typeBindListToNode isActive) tbinds
            , arrangeKidAI cursorOnlyInfo (ctrListToNode isActive) ctrs
            , arrangeKidAI aboveInfo (termToNode isActive) body
            ]
    , tlet:
        \md tyBind tyBinds def body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI cursorOnlyInfo (typeBindToNode isActive) tyBind
            , arrangeKidAI cursorOnlyInfo (typeBindListToNode isActive) tyBinds
            , arrangeKidAI cursorOnlyInfo (typeToNode isActive) def
            , arrangeKidAI aboveInfo (termToNode isActive) body
            ]
    , typeBoundary:
        \md ch t ->
          arrangeTerm args
            [ arrangeKidAI aboveInfo (termToNode isActive) t
            , arrangeKidAI cursorOnlyInfo (const changeToNode) { ch, ctxs: term.ctxs }
            ]
    , contextBoundary:
        \md x c t ->
          arrangeTerm args
            [ arrangeKidAI aboveInfo (termToNode isActive) t
            ]
    , hole:
        \md ->
          setNodeMetadata (makeHoleMetadata (typeToNode false AINothing { ctxs: term.ctxs, ty: term.ty }))
            $ arrangeTerm args
                [ arrangeKidAI cursorOnlyInfo (insideHoleToNode isActive) { ctxs: term.ctxs, ty: term.ty }
                ]
    --          let
    --            getCursor =
    --              join
    --                $ justWhen args.isActive \_ -> do
    --                    cursorLocation <- args.makeCursor unit
    --                    Just (_ { mode = makeCursorMode cursorLocation })
    --          in
    --            makeNode
    --              { kids: [ typeToNode false AINothing { ctxs: term.ctxs, ty: term.ty } ]
    --              , getCursor: getCursor
    --              , getSelect:
    --                  join
    --                    $ justWhen args.isActive \_ -> do
    --                        select <- args.makeSelect unit
    --                        if List.null (getMiddlePath select) then
    --                          getCursor
    --                        else
    --                          Just (_ { mode = makeSelectMode select })
    --              , tag: termToNodeTag term.term
    --              }
    , buffer:
        \md def defTy body _bodyTy ->
          arrangeTerm args
            [ arrangeKidAI aboveInfo (termToNode isActive) def
            , arrangeKidAI cursorOnlyInfo (typeToNode isActive) defTy
            , arrangeKidAI aboveInfo (termToNode isActive) body
            ]
    }
    term
  where
  args =
    { isActive
    , makeCursor: justWhen isActive \_ -> TermCursor term.ctxs term.ty (aIGetPath aboveInfo) term.term
    , makeSelect:  
        case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx (topTerm /\ topTy) midPath -> justWhen isActive \_ -> TermSelect topPath topCtx topTy topTerm midPath term.ctxs term.ty term.term topSelectOrientation
          AINothing -> Nothing
    , term
    }

  cursorOnlyInfo :: forall a. AboveInfo a
  cursorOnlyInfo = aIOnlyCursor aboveInfo

-- ** Type
-- | here is where indentation and parenthesization happens
stepKidsType :: Boolean -> Type -> Array PreNode -> Array Node
stepKidsType isActive ty kids = case ty of
  Arrow md ty1 ty2
    | [ k_ty1, k_ty2 ] <- kids ->
      [ let node = k_ty1 (Arrow1 md ty2) in setNodeIsParenthesized (getNodeTag node == ArrowNodeTag) node
      , setNodeIndentation (indentIf isActive md.codIndented) $ k_ty2 (Arrow2 md ty1)
      ]
  TNeu md x args
    | [ k_args ] <- kids -> [ addNodeStyle (NodeStyle "list-head-var") $ k_args (TNeu1 md x) ]
  THole md id _ _
    | [] <- kids -> []
  _ -> unsafeThrow "stepKidsType: wrong number of kids"

type TypeNodeCursorInfo
  = { isActive :: Boolean
    , ty :: TypeRecValue
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    }

arrangeType ::
  TypeNodeCursorInfo ->
  Array PreNode ->
  Node
arrangeType args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: typeToNodeTag args.ty.ty
    , stepKids: stepKidsType args.isActive args.ty.ty
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

typeToNode :: Boolean -> AboveInfo Type -> TypeRecValue -> Node
typeToNode isActive aboveInfo ty =
  --  trace ("typeToNode called on ty: " <> show ty) \_ ->
  recType
    { arrow:
        \md ty1 ty2 ->
          arrangeType args
            [ arrangeKidAI aboveInfo (typeToNode isActive) ty1
            , arrangeKidAI aboveInfo (typeToNode isActive) ty2
            ]
    , tNeu:
        \md x tyArgs ->
          let
            wrap = case x of
              (CtxBoundaryTypeVar _kind _mtd _name _x) -> makeWrapperNode TContextBoundaryNodeTag
              _ -> \node -> node
          in
            wrap $ setNodeMetadata (makeTNeuNodeMetadata (typeVarGetName ty.ctxs.mdkctx x))
              $ arrangeType args
                  [ arrangeKidAI ai (typeArgListToNode isActive) tyArgs
                  ]
    , tHole:
        \md x weakenings substitutions ->
          setNodeMetadata
            ( makeTHoleNodeMetadata
                x
                ( (\tyVarID -> typeVarGetName ty.ctxs.mdkctx (TypeVar tyVarID))
                    <$> Set.toUnfoldable weakenings
                )
                -- TODO: need to get the tyVarID's name in a special way, since
                -- its not in scope
                ( ( \(_tyVarID /\ type_) ->
                      { typeVarID: "<todo>" -- typeVarGetName ty.ctxs.mdkctx (TypeVar tyVarID)
                      , type_: typeToNode false AINothing { ctxs: ty.ctxs, ty: type_ }
                      }
                  )
                    <$> Map.toUnfoldable substitutions
                )
            )
            $ arrangeType args []
    }
    ty
  where
  args =
    { isActive
    , makeCursor: justWhen isActive \_ -> TypeCursor ty.ctxs (aIGetPath aboveInfo) ty.ty
    , makeSelect:
        case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx topTy midPath -> justWhen isActive \_ -> TypeSelect topPath topCtx topTy midPath ty.ctxs ty.ty topSelectOrientation
          AINothing -> Nothing
    , ty
    }

  ai :: forall a. AboveInfo a
  ai = aIOnlyCursor aboveInfo

stepKidsCtr :: Boolean -> Constructor -> Array PreNode -> Array Node
stepKidsCtr isActive (Constructor md tBind ctrParams) [ k_tBind, k_ctrParams ] =
  [ k_tBind (Constructor1 md {--} ctrParams)
  , addNodeStyle (NodeStyle "list-head") $ k_ctrParams (Constructor2 md tBind {--})
  ]

stepKidsCtr _ _ _ = unsafeThrow "stepKidsCtr: wrong number of kids"

type CtrNodeCursorInfo
  = { isActive :: Boolean
    , ctr :: CtrRecValue
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    }

arrangeCtr ::
  CtrNodeCursorInfo ->
  Array PreNode ->
  Node
arrangeCtr args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: ConstructorNodeTag -- There is only one tag for constructor
    , stepKids: stepKidsCtr args.isActive args.ctr.ctr
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

-- Constructor
ctrToNode :: Boolean -> AboveInfo Constructor -> CtrRecValue -> Node
ctrToNode isActive aboveInfo ctr =
  recCtr
    { ctr:
        \md tBind ctrParams ->
          arrangeCtr
            { isActive
            , makeCursor: Nothing
            , makeSelect: Nothing
            , ctr
            }
            [ arrangeKidAI cursorOnlyAI (termBindToNode isActive) tBind
            , arrangeKidAI cursorOnlyAI (ctrParamListToNode isActive) ctrParams
            ]
    }
    ctr
  where
  cursorOnlyAI :: forall a. AboveInfo a
  cursorOnlyAI = aIOnlyCursor aboveInfo

-- CtrParam
--
--ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
--ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
--    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
--    , kids: [[typeToNode isActive (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
--    , getCursor: Nothing
--    , getSelect: Nothing
--    , style: makeNormalNodeStyle
stepKidsCtrParam :: Boolean -> CtrParam -> Array PreNode -> Array Node
stepKidsCtrParam isActive (CtrParam md ty) [ k_ty ] = [ k_ty (CtrParam1 md {--}) ]

stepKidsCtrParam _ _ _ = unsafeThrow "stepKidsCtrParam: wrong number of kids"

type CtrParamNodeCursorInfo
  = { isActive :: Boolean, ctrParam :: CtrParamRecValue }

arrangeCtrParam :: CtrParamNodeCursorInfo -> Array PreNode -> Node
arrangeCtrParam args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: CtrParamNodeTag
    , stepKids: stepKidsCtrParam args.isActive args.ctrParam.ctrParam
    , makeCursor: Nothing
    , makeSelect: Nothing
    }

ctrParamToNode :: Boolean -> AboveInfo CtrParam -> CtrParamRecValue -> Node
ctrParamToNode isActive aboveInfo ctrParam =
  recCtrParam
    { ctrParam:
        \md ty ->
          arrangeCtrParam
            { isActive
            , ctrParam
            }
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (typeToNode isActive) ty
            ]
    }
    ctrParam

stepKidsTypeArg :: Boolean -> TypeArg -> Array PreNode -> Array Node
stepKidsTypeArg isActive (TypeArg md ty) [ k_ty ] = [ k_ty (TypeArg1 md {--}) ]

stepKidsTypeArg _ _ _ = unsafeThrow "stepKidsTypeArg: wrong number of kids"

type TypeArgNodeCursorInfo
  = { isActive :: Boolean
    , tyArg :: TypeArgRecValue
    }

-- TypeArg
arrangeTypeArg :: TypeArgNodeCursorInfo -> Array PreNode -> Node
arrangeTypeArg args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: TypeArgNodeTag
    , stepKids: stepKidsTypeArg args.isActive args.tyArg.tyArg
    , makeCursor: Nothing
    , makeSelect: Nothing
    }

typeArgToNode :: Boolean -> AboveInfo TypeArg -> TypeArgRecValue -> Node
typeArgToNode isActive aboveInfo tyArg =
  recTypeArg
    { typeArg:
        \md ty ->
          arrangeTypeArg
            { isActive, tyArg
            }
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (typeToNode isActive) ty
            ]
    }
    tyArg

-- TypeBind
typeBindToNode :: Boolean -> AboveInfo Unit -> TypeBindRecValue -> Node
typeBindToNode isActive aboveInfo { ctxs, tyBind: tyBind@(TypeBind md x) } =
  setNodeMetadata (makeTypeBindNodeMetadata md.varName)
    $ makeNode
        { kids: []
        , getCursor:
            justWhen isActive \_ -> _ { mode = makeCursorMode $ TypeBindCursor ctxs (aIGetPath aboveInfo) tyBind }
        , getSelect: Nothing
        , tag: TypeBindNodeTag
        }

stepKidsTypeBindList :: Boolean -> List TypeBind -> Array PreNode -> Array Node
stepKidsTypeBindList isActive tyBinds kids = case tyBinds of
  Nil
    | [] <- kids -> []
  tyBind@(TypeBind md _) : tyBinds'
    | [ k_tyBind, k_tyBinds ] <- kids ->
      [ k_tyBind (TypeBindListCons1 {--} tyBinds')
      , k_tyBinds (TypeBindListCons2 tyBind {--})
      ]
  _ -> unsafeThrow "stepKidsTypeBindList: wrong number of kids"

type TypeBindListNodeCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    , tyBinds :: ListTypeBindRecValue
    }

arrangeTypeBindList :: TypeBindListNodeCursorInfo -> Array PreNode -> Node
arrangeTypeBindList args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: tyBindListToNodeTag args.tyBinds.tyBinds
    , stepKids: stepKidsTypeBindList args.isActive args.tyBinds.tyBinds
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

-- TypeBind
typeBindListToNode :: Boolean -> AboveInfo (List TypeBind) -> ListTypeBindRecValue -> Node
typeBindListToNode isActive aboveInfo tyBinds =
  recListTypeBind
    { cons:
        \tyBind tyBinds ->
          arrangeTypeBindList args
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (typeBindToNode isActive) tyBind
            , arrangeKidAI aboveInfo (typeBindListToNode isActive) tyBinds
            ]
    , nil: \_ -> arrangeTypeBindList args []
    }
    tyBinds
  where
  args =
    { isActive
    , makeCursor: justWhen isActive \_ ->  TypeBindListCursor tyBinds.ctxs (aIGetPath aboveInfo) tyBinds.tyBinds
    , makeSelect:
        case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx topTyBinds midPath -> justWhen isActive \_ ->  TypeBindListSelect topPath topCtx topTyBinds midPath tyBinds.ctxs tyBinds.tyBinds topSelectOrientation
          AINothing -> Nothing
    , tyBinds
    }

-- TermBind
termBindToNode :: Boolean -> AboveInfo Unit -> TermBindRecValue -> Node
termBindToNode isActive aboveInfo { ctxs, tBind: tBind@(TermBind md x) } =
  setNodeMetadata (makeTermBindNodeMetadata md.varName)
    $ makeNode
        { kids: []
        , getCursor:
            justWhen isActive \_ -> _ { mode = makeCursorMode $ TermBindCursor ctxs (aIGetPath aboveInfo) tBind }
        , getSelect: Nothing
        , tag: TermBindNodeTag
        }

type CtrParamListNodeCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    , ctrParams :: ListCtrParamRecValue
    }

arrangeCtrParamList :: CtrParamListNodeCursorInfo -> Array PreNode -> Node
arrangeCtrParamList args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: ctrParamListToNodeTag args.ctrParams.ctrParams
    , stepKids: stepKidsCtrParamList args.isActive args.ctrParams.ctrParams
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

stepKidsCtrParamList :: Boolean -> List CtrParam -> Array PreNode -> Array Node
stepKidsCtrParamList isActive ctrParams kids = case ctrParams of
  Nil
    | [] <- kids -> []
  ctrParam@(CtrParam md _) : ctrParams'
    | [ k_ctrParam, k_ctrParams ] <- kids ->
      [ k_ctrParam (CtrParamListCons1 {--} ctrParams')
      , setNodeIndentation (indentIf isActive md.indented) $ k_ctrParams (CtrParamListCons2 ctrParam {--})
      ]
  _ -> unsafeThrow "stepKidsCtrParamList: wrong number of kids"

-- CtrParamList
ctrParamListToNode :: Boolean -> AboveInfo (List CtrParam) -> ListCtrParamRecValue -> Node
ctrParamListToNode isActive aboveInfo ctrParams =
  recListCtrParam
    { cons:
        \ctrParam ctrParams ->
          arrangeCtrParamList args
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (ctrParamToNode isActive) ctrParam
            , arrangeKidAI aboveInfo (ctrParamListToNode isActive) ctrParams
            ]
    , nil: \_ -> arrangeCtrParamList args []
    }
    ctrParams
  where
  args =
    { isActive
    , makeCursor: justWhen isActive \_ ->  CtrParamListCursor ctrParams.ctxs (aIGetPath aboveInfo) ctrParams.ctrParams
    , makeSelect:
        case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx topCtrParams midPath -> justWhen isActive \_ ->  CtrParamListSelect topPath topCtx topCtrParams midPath ctrParams.ctxs ctrParams.ctrParams topSelectOrientation
          AINothing -> Nothing
    , ctrParams
    }

stepKidsTypeArgList :: Boolean -> List TypeArg -> Array PreNode -> Array Node
stepKidsTypeArgList isActive tyArgs kids = case tyArgs of
  Nil
    | [] <- kids -> []
  tyArg@(TypeArg md _) : tyArgs'
    | [ k_tyArg, k_tyArgs ] <- kids ->
      [ k_tyArg (TypeArgListCons1 {--} tyArgs')
      , setNodeIndentation (indentIf isActive md.indented) $ k_tyArgs (TypeArgListCons2 tyArg {--})
      ]
  _ -> unsafeThrow "stepKidsTypeArgList: wrong number of kids"

type TypeArgListNodeCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    , tyArgs :: ListTypeArgRecValue
    }

arrangeTypeArgList :: TypeArgListNodeCursorInfo -> Array PreNode -> Node
arrangeTypeArgList args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: tyArgListToNodeTag args.tyArgs.tyArgs
    , stepKids: stepKidsTypeArgList args.isActive args.tyArgs.tyArgs
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

-- ArgParamList
typeArgListToNode :: Boolean -> AboveInfo (List TypeArg) -> ListTypeArgRecValue -> Node
typeArgListToNode isActive aboveInfo tyArgs =
  recListTypeArg
    { cons:
        \tyArg tyArgs ->
          arrangeTypeArgList args
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (typeArgToNode isActive) tyArg
            , arrangeKidAI aboveInfo (typeArgListToNode isActive) tyArgs
            ]
    , nil: \_ -> arrangeTypeArgList args []
    }
    tyArgs
  where
  args =
    { isActive
    , makeCursor: Nothing -- \_ -> Just $ TypeArgListCursor tyArgs.ctxs (aIGetPath aboveInfo) tyArgs.tyArgs
    , makeSelect: Nothing
    --            \_ -> case aboveInfo of
    --                AICursor _path -> Nothing
    --                AISelect topPath topCtx topTypeArgs midPath -> Just $ TypeArgListSelect topPath topCtx topTypeArgs midPath tyArgs.ctxs tyArgs.tyArgs topSelectOrientation
    --                AINothing -> Nothing
    , tyArgs
    }

stepKidsCtrList :: Boolean -> List Constructor -> Array PreNode -> Array Node
stepKidsCtrList isActive ctrs kids = case ctrs of
  Nil
    | [] <- kids -> []
  ctr@(Constructor md _ _) : ctrs'
    | [ k_ctr, k_ctrs ] <- kids ->
      [ k_ctr (CtrListCons1 {--} ctrs')
      , setNodeIndentation (indentIf isActive md.indented) $ k_ctrs (CtrListCons2 ctr {--})
      ]
  _ -> unsafeThrow ("stepKidsCtrList: wrong number of kids. Kids length is: " <> show (Array.length kids) <> "while ctrs is: " <> show ctrs)

type CtrListNodeCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    , ctrs :: ListCtrRecValue
    }

arrangeCtrList :: CtrListNodeCursorInfo -> Array PreNode -> Node
arrangeCtrList args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: ctrListToNodeTag args.ctrs.ctrs
    , stepKids: stepKidsCtrList args.isActive args.ctrs.ctrs
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }

-- ConstructorList
ctrListToNode :: Boolean -> AboveInfo (List Constructor) -> ListCtrRecValue -> Node
ctrListToNode isActive aboveInfo ctrs =
  recListCtr
    { cons:
        \ctr ctrs ->
          arrangeCtrList args
            [ arrangeKidAI (aIOnlyCursor aboveInfo) (ctrToNode isActive) ctr
            , arrangeKidAI aboveInfo (ctrListToNode isActive) ctrs
            ]
    , nil: \_ -> arrangeCtrList args []
    }
    ctrs
  where
  args =
    { isActive
    , makeCursor: justWhen isActive \_ ->  CtrListCursor ctrs.ctxs (aIGetPath aboveInfo) ctrs.ctrs
    , makeSelect:
        case aboveInfo of
          AICursor _path -> Nothing
          AISelect topPath topCtx topCtrs midPath -> justWhen isActive \_ ->  CtrListSelect topPath topCtx topCtrs midPath ctrs.ctxs ctrs.ctrs topSelectOrientation
          AINothing -> Nothing
    , ctrs
    }

stepInsideHoleKids :: Array PreNode -> Array Node
stepInsideHoleKids [] = []

stepInsideHoleKids _ = unsafeThrow "insideHole doesn't have kids"

type InsideHoleCursorInfo
  = { isActive :: Boolean
    , makeCursor :: Maybe CursorLocation
    , makeSelect :: Maybe Select
    }

arrangeInsideHole :: InsideHoleCursorInfo -> Node
arrangeInsideHole args =
  arrangeNodeKids
    { isActive: args.isActive
    , tag: HoleInnerNodeTag
    , stepKids: stepInsideHoleKids
    , makeCursor: args.makeCursor
    , makeSelect: args.makeSelect
    }
    []

insideHoleToNode :: Boolean -> AboveInfo Unit -> InsideHoleRecValue -> Node
insideHoleToNode isActive aboveInfo inside =
  arrangeInsideHole
    { isActive
    , makeCursor: justWhen isActive \_ ->  InsideHoleCursor inside.ctxs inside.ty (aIGetPath aboveInfo)
    , makeSelect: Nothing
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
          [ parenthesizeChangeChildNode ch1 $ changeToNode val { ch = ch1 }
          , parenthesizeChangeChildNode ch2 $ changeToNode val { ch = ch2 }
          ]
      }
  CHole holeId wkn sigma ->
    setNodeMetadata
      ( makeTHoleNodeMetadata holeId
          ((typeVarGetName val.ctxs.mdkctx <<< TypeVar) <$> Set.toUnfoldable wkn)
          ( ( \(_typeVarId /\ subChange) -> case subChange of
                SubTypeChange ch -> { typeVarID: "TODO", type_: changeToNode { ch, ctxs: val.ctxs } }
                SubDelete ty -> { typeVarID: "TODO", type_: typeToNode false dummyAboveInfo { ty, ctxs: val.ctxs } }
                SubInsert ty -> { typeVarID: "TODO", type_: typeToNode false dummyAboveInfo { ty, ctxs: val.ctxs } }
            )
              <$> Map.toUnfoldable sigma
          )
      )
      $ makeChangeNode
          { tag: THoleNodeTag
          , kids: []
          }
  Replace ty1 ty2 ->
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
          , parenthesizeChangeChildNode ch $ changeToNode val { ch = ch }
          ]
      }
  Minus ty ch ->
    makeChangeNode
      { tag: MinusNodeTag
      , kids:
          [ changeToNode val { ch = ch }
          , parenthesizeChangeChildNode ch $ typeToNode false dummyAboveInfo { ctxs: val.ctxs, ty }
          ]
      }
  CNeu cTypeVar _args ->
    setNodeMetadata
      ( makeTNeuNodeMetadata case cTypeVar of
          CTypeVar x -> typeVarGetName val.ctxs.mdkctx (TypeVar x)
          CCtxBoundaryTypeVar _k _mb_typeDefVal str _typeVarID -> "{{" <> str <> "}}"
          PlusCtxBoundaryTypeVar _k _mb_typeDefVal str _typeVarID -> "+" <> str
          MinusCtxBoundaryTypeVar _k _mb_typeDefVal str _typeVarID -> "-" <> str
      )
      $ makeChangeNode
          { tag: TNeuNodeTag
          , kids: [] -- TODO: type args  -- Note from Jacob: Having 0 kids caused a crash, so I hacked a temporary solution in Frontend.tsx. When we fix this, remember to remove that temporary fix.
          }

parenthesizeChangeChildNode :: Change -> Node -> Node
parenthesizeChangeChildNode ch =
  setNodeIsParenthesized case ch of
    CArrow _ _ -> true
    CHole _ _ _ -> false
    Replace _ _ -> true
    Plus _ _ -> true
    Minus _ _ -> true
    CNeu _ args -> not $ List.null args

-- since this will never be used for non-cursorable things
-- TODO: make AboveInfo a Maybe, so that when its nothing covers the false
-- Boolean case in *toNode functions
dummyAboveInfo :: forall a. AboveInfo a
dummyAboveInfo = AICursor Nil
