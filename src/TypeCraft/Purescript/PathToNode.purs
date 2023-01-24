module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, DownPath, Term, Tooth(..), Type, TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.Node (Node, NodeTag(..), makeNode)
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode)
import TypeCraft.Purescript.Util (hole, hole', justWhen)
import TypeCraft.Purescript.TermToNode

data BelowInfo term ty -- NOTE: a possible refactor is to combine term and ty into syn like in TermToNode. On the other hand, I'll probably never bother.
  = BITerm
  | BISelect DownPath term AllContext ty -- middle path, then bottom term. ctx and ty are the type and context of term.

{-
stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
stepBI tooth (BITerm syn) = BITerm (step syn)
stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
stepBI = hole
-}
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!
-- TODO: @jacob think about this
stepBI :: forall syn synty. Tooth -> BelowInfo syn synty -> BelowInfo syn synty
stepBI _tooth BITerm = BITerm

stepBI tooth (BISelect middle bottom ctxs ty) = BISelect (tooth : middle) bottom ctxs ty

arrangeKid :: forall a recVal. UpPath -> (AboveInfo a -> recVal -> Node) -> recVal -> PreNode
arrangeKid path k rv th = k (AICursor (th : path)) rv

--arrangeKid :: forall term ty rc. BelowInfo term ty -> (BelowInfo term ty -> rc -> Node) -> rc -> PreNode
--arrangeKid bi k rc ind th = setNodeIndentation ind $ k (stepBI th bi) rc
type PartialNode
  = { kids :: Array Node
    , tag :: NodeTag
    }

-- arrangeKidBI :: forall a b recVal. (recVal -> UpPath) -> BelowInfo a b -> (BelowInfo a b -> recVal -> Node) -> recVal -> PreNode
-- arrangeKidBI toUpPath = arrangeKid (\rv th bi -> )
makeTermNode :: Boolean -> BelowInfo Term Type -> TermPathRecValue -> PartialNode -> Node
makeTermNode isActive belowInfo termPath preNode =
  makeNode
    { kids: {-setCalculatedNodeData preNode.tag <$> -} preNode.kids
    , getCursor:
        justWhen isActive \_ ->
          _ { mode = makeCursorMode $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term }
    , getSelect:
        case belowInfo of
          BITerm -> Nothing
          BISelect middlePath term ctxs ty ->
            justWhen isActive \_ ->
              _ { mode = SelectMode $ { select: TermSelect termPath.termPath termPath.ctxs termPath.ty termPath.term middlePath ctxs ty term true } }
    , tag: preNode.tag
    }

-- The MDType is for the top of the path (which is the end of the list)
termPathToNode :: Boolean -> BelowInfo Term Type -> TermPathRecValue -> (Node -> Node)
termPathToNode _isActive _ { termPath: Nil } node = node

termPathToNode isActive belowInfo termPath innerNode =
  let
    term = termPath.term
  in
    recTermPath
      { let3:
          \upRecVal md tBind tyBinds {-def-} ty body bodyTy ->
            let newBI = (stepBI (Let3 md tBind.tBind tyBinds.tyBinds ty.ty body.term bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (termBindToNode isActive) tBind
                  , arrangeKid upRecVal.termPath (typeBindListToNode isActive) tyBinds
                  , arrangeKid upRecVal.termPath (typeToNode isActive) ty
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  , arrangeKid upRecVal.termPath (termToNode isActive) body
                  ]
      , app1:
          \upRecVal md {-Term-} t2 argTy bodyTy ->
            let newBI = (stepBI (App1 md {-t1-} t2.term argTy bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  , arrangeKid upRecVal.termPath (termToNode isActive) t2
                  ]
      , app2:
          \upRecVal md t1 {-Term-} argTy bodyTy ->
            let newBI = (stepBI (App2 md {--} t1.term argTy bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (termToNode isActive) t1
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  ]
      , lambda3:
          \upRecVal md tBind argTy {-body-} bodyTy ->
            let newBI = (stepBI (Lambda3 md tBind.tBind argTy.ty bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (termBindToNode isActive) tBind
                  , arrangeKid upRecVal.termPath (typeToNode isActive) argTy
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  ]
      , buffer1: \upRecVal md {-Term-} bufTy body bodyTy -> hole' "termPathToNode 1"
      , buffer3: \upRecVal md buf bufTy {-Term-} bodyTy -> hole' "termPathToNode 2"
      , typeBoundary1: \upRecVal md change {-Term-} -> hole' "termPathToNode 3"
      , contextBoundary1: \upRecVal md x change {-Term-} -> hole' "termPathToNode 4"
      , tLet4:
          \upRecVal md tyBind tyBinds def {-Term-} bodyTy ->
            let newBI = (stepBI (TLet4 md tyBind tyBinds.tyBinds def.ty bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (typeBindToNode isActive) { ctxs: upRecVal.ctxs, tyBind }
                  , arrangeKid upRecVal.termPath (typeBindListToNode isActive) tyBinds
                  , arrangeKid upRecVal.termPath (typeToNode isActive) def
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  ]
      , let5:
          \upRecVal md tBind tyBinds def ty {-body-} bodyTy ->
            let newBI = (stepBI (Let5 md tBind.tBind tyBinds.tyBinds def.term ty.ty {-body-} bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (termBindToNode isActive) tBind
                  , arrangeKid upRecVal.termPath (typeBindListToNode isActive) tyBinds
                  , arrangeKid upRecVal.termPath (typeToNode isActive) ty
                  , arrangeKid upRecVal.termPath (termToNode isActive) def
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  ]
      , data4:
          \upRecVal md tyBind tyBinds ctrs {-body-} bodyTy ->
            let newBI = (stepBI (Data4 md tyBind.tyBind tyBinds.tyBinds ctrs.ctrs {-body-} bodyTy) belowInfo) in
            termPathToNode isActive newBI upRecVal
              $ arrangeTerm (makeTermArgs isActive newBI upRecVal)
                  [ arrangeKid upRecVal.termPath (typeBindToNode isActive) tyBind
                  , arrangeKid upRecVal.termPath (typeBindListToNode isActive) tyBinds
                  , arrangeKid upRecVal.termPath (ctrListToNode isActive) ctrs
                  , arrangeKid upRecVal.termPath (\_ _ -> innerNode) term
                  ]
      }
      termPath
makeTermArgs :: Boolean -> BelowInfo Term Type -> TermPathRecValue -> TermNodeCursorInfo
makeTermArgs isActive belowInfo upRecVal =
    { isActive
    , makeCursor: \_ -> Just $ TermCursor upRecVal.ctxs upRecVal.ty upRecVal.termPath upRecVal.term
    , makeSelect:
        \_ -> case belowInfo of
          BITerm -> Nothing
          BISelect middlePath term ctxs ty -> Just $ TermSelect upRecVal.termPath upRecVal.ctxs upRecVal.ty upRecVal.term middlePath ctxs ty term true
    , term: { ctxs: upRecVal.ctxs, term: upRecVal.term, ty: upRecVal.ty }
    }

makeTypeArgs :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> TypeNodeCursorInfo
makeTypeArgs isActive belowInfo urv =
    { isActive
    , makeCursor: \_ -> Just $ TypeCursor urv.ctxs urv.typePath urv.ty
    , makeSelect:
        \_ -> case belowInfo of
          BITerm -> Nothing
          BISelect middlePath ty ctxs _ -> Just $ TypeSelect urv.typePath urv.ctxs urv.ty middlePath ctxs ty true
    , ty: { ctxs: urv.ctxs, ty: urv.ty }
    }

typePathToNode :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
typePathToNode isActive _ { typePath: Nil } node = node

typePathToNode isActive belowInfo typePath innerNode =
  let
    ty = typePath.ty
  -- makeTypeNode belowInfo typePath partialNode =
  --   makeNode
  --     { kids: partialNode.kids
  --     , getCursor:
  --         let
  --           belowType = case belowInfo of
  --             BITerm -> typePath.ty
  --             BISelect middlePath term _ _ -> typePath.ty -- TODO: combineDownPathTerm middlePath term
  --         in
  --           justWhen isActive \_ ->
  --             _ { mode = makeCursorMode $ TypeCursor typePath.ctxs typePath.typePath belowType }
  --     , getSelect: Nothing
  --     , tag: partialNode.tag
  --     }
  in
    recTypePath
      ( { lambda2:
            \termPath md tBind {-Type-} body bodyTy ->
              let newBI = BITerm in
              termPathToNode isActive newBI termPath
                $ arrangeTerm (makeTermArgs isActive newBI termPath)
                    [ arrangeKid termPath.termPath (termBindToNode isActive) tBind
                    , arrangeKid termPath.termPath (\_ _ -> innerNode) ty
                    , arrangeKid termPath.termPath (termToNode isActive) body
                    ]
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy ->
              let newBI = BITerm in
              termPathToNode isActive newBI termPath
                $ arrangeTerm (makeTermArgs isActive newBI termPath)
                    [ arrangeKid termPath.termPath (termBindToNode isActive) tBind
                    , arrangeKid termPath.termPath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath (\_ _ -> innerNode) ty
                    , arrangeKid termPath.termPath (termToNode isActive) def
                    , arrangeKid termPath.termPath (termToNode isActive) body
                    ]
        , buffer2: \termPath md def {-Type-} body bodyTy -> (hole' "typePathToNode isActive")
        , tLet3:
            \termPath md tyBind tyBinds {-Type-} body bodyTy ->
              let newBI = BITerm in
              termPathToNode isActive newBI termPath
                $ arrangeTerm (makeTermArgs isActive newBI termPath)
                    [ arrangeKid termPath.termPath (typeBindToNode isActive) tyBind
                    , arrangeKid termPath.termPath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath (\_ _ -> innerNode) ty
                    , arrangeKid termPath.termPath (termToNode isActive) body
                    ]
        , ctrParam1: \ctrParamPath md {-Type-} -> (hole' "typePathToNode isActive")
        , typeArg1: \typeArgPath md {-Type-} -> (hole' "typePathToNode isActive")
        , arrow1:
            \typePath md tyOut {-Type-} ->
              let newBI = (stepBI (Arrow1 md tyOut.ty) belowInfo) in
              typePathToNode isActive newBI typePath
                $ arrangeType (makeTypeArgs isActive newBI typePath)
                    [ arrangeKid typePath.typePath (\_ _ -> innerNode) ty
                    , arrangeKid typePath.typePath (typeToNode isActive) tyOut
                    ]
        , arrow2:
            \typePath md tyIn {-Type-} ->
              let newBI = (stepBI (Arrow2 md tyIn.ty) belowInfo) in
              typePathToNode isActive newBI typePath
                $ arrangeType (makeTypeArgs isActive newBI typePath)
                    [ arrangeKid typePath.typePath (typeToNode isActive) tyIn
                    , arrangeKid typePath.typePath (\_ _ -> innerNode) ty
                    ]
        }
      )
      typePath

constructorPathToNode :: Boolean -> AllContext -> BelowInfo Constructor Unit -> UpPath -> Node -> Node
constructorPathToNode isActive ctxs belowInfo up innerNode = (hole' "constructorPathToNode isActive")

ctrParamPathToNode :: Boolean -> AllContext -> BelowInfo CtrParam Unit -> UpPath -> Node -> Node
ctrParamPathToNode isActive ctxs belowInfo up innerNode = (hole' "ctrParamPathToNode isActive")

typeArgPathToNode :: Boolean -> AllContext -> BelowInfo TypeArg Unit -> UpPath -> Node -> Node
typeArgPathToNode isActive ctxs belowInfo up innerNode = (hole' "typeArgPathToNode isActive")

typeBindPathToNode :: Boolean -> TypeBindPathRecValue -> Node -> Node
typeBindPathToNode isActive { typeBindPath: Nil } innerNode = innerNode

typeBindPathToNode isActive typeBindPath innerNode =
  let
    tyBind = typeBindPath.tyBind
  in
    recTypeBindPath
      { tLet1:
          \termPath md {-tyBind-} tyBinds def body bodyTy ->
            let
              newBI = BITerm
            in
              termPathToNode isActive newBI termPath
                $ makeTermNode isActive newBI termPath
                    { tag: TLetNodeTag
                    , kids:
                        [ innerNode
                        , typeBindListToNode isActive (AICursor (TLet2 md tyBind {-tyBinds-} def.ty body.term bodyTy : termPath.termPath)) tyBinds
                        , typeToNode isActive (AICursor (TLet3 md tyBind tyBinds.tyBinds {-def-} body.term bodyTy : termPath.termPath)) def
                        , termToNode isActive (AICursor (TLet4 md tyBind tyBinds.tyBinds def.ty {-body-} bodyTy : termPath.termPath)) body
                        ]
                    }
      , data1:
          \termPath md {-tyBind-} tyBinds ctrs body bodyTy ->
            let
              newBI = BITerm
            in
              termPathToNode isActive newBI termPath
                $ makeTermNode isActive newBI termPath
                    { tag: DataNodeTag
                    , kids:
                        stepKidsTerm termPath.term
                          [ const innerNode
                          , \th -> typeBindListToNode isActive (AICursor (th : termPath.termPath)) tyBinds
                          , \th -> ctrListToNode isActive (AICursor (th : termPath.termPath)) ctrs
                          , \th -> termToNode isActive (AICursor (th : termPath.termPath)) body
                          ]
                    }
      , typeBindListCons1: \listTypeBindPath {-tyBind-} tyBind -> hole' "typeBindPathToNode"
      }
      typeBindPath

{-
typePathToNode isActive :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
typePathToNode isActive _ { typePath: Nil } node = node
typePathToNode isActive belowInfo typePath innerNode =
-}
termBindPathToNode :: Boolean -> TermBindPathRecValue -> Node -> Node
termBindPathToNode isActive { termBindPath: Nil } innerNode = innerNode

termBindPathToNode isActive termBindPath innerNode =
  let
    tBind = termBindPath.tBind
  in
    recTermBindPath
      { lambda1:
          \termPath md argTy body bodyTy ->
            let
              newBI = BITerm
            in {- (stepBI (Lambda1 md argTy.ty body.term bodyTy) BITerm) -}
              termPathToNode isActive newBI termPath
                $ makeTermNode isActive newBI termPath
                    { kids:
                        [ innerNode
                        , typeToNode isActive (AICursor (Lambda2 md tBind body.term bodyTy : termPath.termPath)) argTy
                        , termToNode isActive (AICursor (Lambda3 md tBind argTy.ty bodyTy : termPath.termPath)) body
                        ]
                    , tag: LambdaNodeTag
                    }
      , let1:
          \termPath md tyBinds def defTy body bodyTy ->
            let
              newBI = BITerm
            in {- (stepBI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) BITerm) -}
              termPathToNode isActive newBI termPath
                $ makeTermNode isActive newBI termPath
                    { kids:
                        [ innerNode
                        , typeBindListToNode isActive (AICursor (Let2 md tBind {-List TypeBind-} def.term defTy.ty body.term bodyTy : termPath.termPath)) tyBinds
                        , typeToNode isActive (AICursor ((Let4 md tBind tyBinds.tyBinds def.term body.term bodyTy) : termPath.termPath)) defTy
                        , termToNode isActive (AICursor ((Let3 md tBind tyBinds.tyBinds defTy.ty body.term bodyTy) : termPath.termPath)) def
                        , termToNode isActive (AICursor ((Let5 md tBind tyBinds.tyBinds def.term defTy.ty bodyTy) : termPath.termPath)) body
                        ]
                    , tag: LetNodeTag
                    }
      , constructor1:
          \ctrPath md ctrParams ->
            constructorPathToNode isActive ctrPath.ctxs (stepBI (Constructor1 md ctrParams.ctrParams) BITerm) ctrPath.ctrPath
              $ hole' "termPathBindToNode"
      }
      termBindPath

ctrListPathToNode :: Boolean -> BelowInfo (List Constructor) Unit -> ListCtrPathRecValue -> Node -> Node
ctrListPathToNode belowInfo listCtrPath innerNode = (hole' "ctrListPathToNode")

ctrParamListPathToNode :: Boolean -> BelowInfo (List CtrParam) Unit -> ListCtrParamPathRecValue -> Node -> Node
ctrParamListPathToNode belowInfo listCtrParamPath innerNode = (hole' "ctrParamListPathToNode")

typeArgListPathToNode :: Boolean -> BelowInfo (List TypeArg) Unit -> ListTypeArgPathRecValue -> Node -> Node
typeArgListPathToNode isActive belowInfo listTypeArgPath innerNode = (hole' "typeArgListPathToNode")

typeBindListPathToNode :: Boolean -> BelowInfo (List TypeBind) Unit -> ListTypeBindPathRecValue -> Node -> Node
typeBindListPathToNode isActive belowInfo typeBindListPath innerNode =
  let
    tyBinds = typeBindListPath.tyBinds
  in
    recListTypeBindPath
      ( { data2: \termPath md tyBind ctrs body bodyTy -> hole' "termBindPathToNode isActive"
        , tLet2:
            \termPath md tyBind {-tyBinds-} def body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive newBI termPath
                  $ makeTermNode isActive newBI termPath
                      { tag: TLetNodeTag
                      , kids:
                          [ typeBindToNode isActive (AICursor (TLet1 md {-tyBind-} tyBinds def.ty body.term bodyTy : termPath.termPath)) tyBind
                          , innerNode
                          , typeToNode isActive (AICursor (TLet3 md tyBind.tyBind tyBinds {-def-} body.term bodyTy : termPath.termPath)) def
                          , termToNode isActive (AICursor (TLet4 md tyBind.tyBind tyBinds def.ty {-body-} bodyTy : termPath.termPath)) body
                          ]
                      }
        , typeBindListCons2: \listTypeBindPath tyBind -> hole' "termBindPathToNode isActive"
        , let2:
            \termPath md tBind def defTy body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive newBI termPath
                  $ makeTermNode isActive newBI termPath
                      { kids:
                          [ termBindToNode isActive (AICursor (Let1 md {-tbind-} tyBinds def.term defTy.ty body.term bodyTy : termPath.termPath)) tBind
                          , innerNode
                          , typeToNode isActive (AICursor (Let4 md tBind.tBind tyBinds def.term {-Type-} body.term bodyTy : termPath.termPath)) defTy
                          , termToNode isActive (AICursor (Let3 md tBind.tBind tyBinds {-Term-} defTy.ty body.term bodyTy : termPath.termPath)) def
                          , termToNode isActive (AICursor (Let5 md tBind.tBind tyBinds def.term defTy.ty {-Term-} bodyTy : termPath.termPath)) body
                          ]
                      , tag: LetNodeTag
                      }
        }
      )
      typeBindListPath

{-
Problems currently:
1) *PathToNode are currently not recursive. They should incorporate the teeth rest of the path somehow
2) something something combining teeth with *s causes typing problems?
     remember that when we switch to a different sort we always go to BITerm
3) We need to either 1) draw everything from top down, including paths, or 2) put the MDContext into the State
    TODO TODO TODO ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    The problem with drawing top down is that when detmining the selection, you can't know where is a valid place to
    select to until you traverse UPWARDS from the cursor.
    Another reason to put the metacontext in the state: we actually need it to display queries correctly
-}
