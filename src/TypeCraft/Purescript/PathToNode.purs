module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)

import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Debug (trace)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, DownPath, Term, TermBind, Tooth(..), Type, TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.Node (Node, NodeTag(..), makeNode, setCalculatedNodeData)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode, makeState)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), termBindToNode, termToNode, typeToNode)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermToNode (typeBindListToNode)
import TypeCraft.Purescript.PathRec

data BelowInfo term ty -- NOTE: a possible refactor is to combine term and ty into syn like in TermToNode. On the other hand, I'll probably never bother.
  = BITerm
  | BISelect DownPath term AllContext ty -- middle path, then bottom term. ctx and ty are the type and context of term.

--stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
----stepBI tooth (BITerm syn) = BITerm (step syn)
----stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
--stepBI = hole
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!
stepBI :: forall syn synty. Tooth -> BelowInfo syn synty -> BelowInfo syn synty
stepBI tooth BITerm = BITerm
stepBI tooth (BISelect middle bottom ctxs ty) = BISelect (tooth : middle) bottom ctxs ty

type PreNode = {
    kids :: Array Node
    , tag :: NodeTag
}

makeTermNode :: BelowInfo Term Type -> TermPathRecValue -> PreNode -> Node
makeTermNode belowInfo termPath preNode =
      makeNode
        { kids: preNode.kids <#> setCalculatedNodeData preNode.tag >>> pure
        , getCursor:
            Just \_ ->
              trace ("here termPathToNode" <> show termPath.termPath <> " \nand term is: " <> show termPath.term) \_ ->
              makeState $ makeCursorMode $ TermCursor termPath.ctxs termPath.ty termPath.termPath termPath.term
        , getSelect:
            case belowInfo of
              BITerm -> Nothing
              BISelect middlePath term ctxs ty -> Just \_ -> makeState $ SelectMode $
                {select: TermSelect termPath.termPath termPath.ctxs termPath.ty termPath.term middlePath ctxs ty term true}
        , tag: preNode.tag
        }

-- The MDType is for the top of the path (which is the end of the list)
termPathToNode :: BelowInfo Term Type -> TermPathRecValue -> (Node -> Node)
termPathToNode _ { termPath: Nil } node = node
termPathToNode belowInfo termPath innerNode =
  let
    term = termPath.term
  in
    recTermPath
      ( { let3:
            \upRecVal md tBind tyBinds {-def-} ty body bodyTy ->
              let newBI = (stepBI (Let3 md tBind.tBind tyBinds.tyBinds ty.ty body.term bodyTy) belowInfo) in
              termPathToNode newBI upRecVal
                $ makeTermNode newBI upRecVal
                    { tag: LetNodeTag
                    , kids:
                        [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds.tyBinds term ty.ty body.term bodyTy : upRecVal.termPath)) tBind
                        , typeBindListToNode (AICursor (Let2 md tBind.tBind {-List TypeBind-} term ty.ty body.term bodyTy : upRecVal.termPath)) tyBinds
                        , innerNode
                        , typeToNode (AICursor (Let4 md tBind.tBind tyBinds.tyBinds term {-Type-} body.term bodyTy : upRecVal.termPath)) ty
                        , termToNode (AICursor (Let5 md tBind.tBind tyBinds.tyBinds term ty.ty {-Term-} bodyTy : upRecVal.termPath)) body
                        ]
                    }
        , app1: \upRecVal md {-Term-} t2 argTy bodyTy ->
            let newBI = (stepBI (App1 md {--} t2.term argTy bodyTy) belowInfo) in
            termPathToNode newBI upRecVal
                $ makeTermNode newBI upRecVal
                    { tag: AppNodeTag
                    , kids: [
                            innerNode,
                            termToNode (AICursor (App2 md term argTy bodyTy : upRecVal.termPath)) t2
                        ]
                    }
        , app2: \upRecVal md t1 {-Term-} argTy bodyTy ->
            let newBI = (stepBI (App2 md {--} t1.term argTy bodyTy) belowInfo) in
            termPathToNode newBI upRecVal
                $ makeTermNode newBI upRecVal
                    { tag: AppNodeTag
                    , kids: [
                            termToNode (AICursor (App1 md term argTy bodyTy : upRecVal.termPath)) t1
                            , innerNode
                        ]
                    }
        , lambda3:
            \upRecVal md tBind argTy {-body-} bodyTy ->
            let newBI = (stepBI (Lambda3 md tBind argTy.ty bodyTy) belowInfo) in
              termPathToNode newBI upRecVal
                $ makeTermNode newBI upRecVal
                    { tag: LambdaNodeTag
                    , kids:
                        [ termBindToNode (AICursor (Lambda1 md argTy.ty term bodyTy : upRecVal.termPath)) { ctxs: upRecVal.ctxs, tBind }
                        , typeToNode (AICursor (Lambda2 md tBind term bodyTy : upRecVal.termPath)) argTy
                        , innerNode
                        ]
                    }
        , buffer1: \upRecVal md {-Term-} bufTy body bodyTy -> hole' "termPathToNode"
        , buffer3: \upRecVal md buf bufTy {-Term-} bodyTy -> hole' "termPathToNode"
        , typeBoundary1: \upRecVal md change {-Term-} -> hole' "termPathToNode"
        , contextBoundary1: \upRecVal md x change {-Term-} -> hole' "termPathToNode"
        , tLet4: \upRecVal md tyBind tyBinds def {-Term-} bodyTy -> hole' "termPathToNode"
        , let5: \upRecVal md tBind tyBinds def ty {-body-} bodyTy ->
                  let newBI = (stepBI (Let5 md tBind.tBind tyBinds.tyBinds def.term ty.ty {-body-} bodyTy) belowInfo) in
                  termPathToNode newBI upRecVal
                    $ makeTermNode newBI upRecVal
                        { tag: LetNodeTag
                        , kids:
                            [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds.tyBinds def.term ty.ty term bodyTy : upRecVal.termPath)) tBind
                            , typeBindListToNode (AICursor (Let2 md tBind.tBind {-List TypeBind-} def.term ty.ty term bodyTy : termPath.termPath)) tyBinds
                            , termToNode (AICursor ((Let3 md tBind.tBind tyBinds.tyBinds {-def-} ty.ty term bodyTy) : upRecVal.termPath)) def
                            , typeToNode (AICursor (Let4 md tBind.tBind tyBinds.tyBinds def.term {-Type-} term bodyTy : upRecVal.termPath)) ty
                            , innerNode
                            ]
                        }
        , data4: \upRecVal md tbind tbinds ctrs {-body-} bodyTy -> hole' "termPathToNode"
        }
      )
      termPath

typePathToNode :: BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
typePathToNode _ { typePath: Nil } node = node

typePathToNode belowInfo typePath innerNode =
  let
    ty = typePath.ty

    makeTypeNode belowInfo typePath partialNode =
      makeNode
        { kids: partialNode.kids <#> pure
        , getCursor:
            let
              belowType = case belowInfo of
                BITerm -> typePath.ty
                BISelect middlePath term _ _ -> typePath.ty -- TODO: combineDownPathTerm middlePath term
            in
              Just \_ -> 
                trace "here typePathNode" \_ ->
                makeState $ makeCursorMode $ TypeCursor typePath.ctxs typePath.typePath belowType
        , getSelect: Nothing
        , tag: partialNode.tag
        }
  in
    recTypePath
      ( { lambda2:
            \termPath md tBind {-Type-} body bodyTy ->
              let newBI = BITerm in --(stepBI (Lambda2 md tBind.tBind body.term bodyTy) BITerm) in
              termPathToNode newBI termPath
                $ makeTermNode newBI termPath
                    { kids:
                        [ termBindToNode (AICursor (Lambda1 md ty body.term bodyTy : termPath.termPath)) tBind
                        , innerNode
                        , termToNode (AICursor (Lambda3 md tBind.tBind ty bodyTy : termPath.termPath)) body
                        ]
                    , tag: LambdaNodeTag
                    }
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy ->
              let newBI = BITerm in --(stepBI (Let4 md tBind.tBind tyBinds.tyBinds def.term body.term bodyTy) BITerm) in
              termPathToNode newBI termPath
                $ makeTermNode newBI termPath
                    { kids:
                        [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds.tyBinds def.term typePath.ty body.term bodyTy : termPath.termPath)) tBind
                        , typeBindListToNode (AICursor (Let2 md tBind.tBind {-List TypeBind-} def.term ty body.term bodyTy : termPath.termPath)) tyBinds
                        , termToNode (AICursor (Let3 md tBind.tBind tyBinds.tyBinds {-Term-} typePath.ty body.term bodyTy : termPath.termPath)) def
                        , innerNode
                        , termToNode (AICursor (Let5 md tBind.tBind tyBinds.tyBinds def.term typePath.ty {-Term-} bodyTy : termPath.termPath)) body
                        ]
                    , tag: LetNodeTag
                    }
        , buffer2: \termPath md def {-Type-} body bodyTy -> (hole' "typePathToNode")
        , tLet3: \termPath md tyBind tyBinds {-Type-} body bodyTy -> (hole' "typePathToNode")
        , ctrParam1: \ctrParamPath md {-Type-} -> (hole' "typePathToNode")
        , typeArg1: \typeArgPath md {-Type-} -> (hole' "typePathToNode")
        , arrow1: \typePath md tyOut {-Type-} ->
            let newBI = stepBI (Arrow1 md tyOut.ty) belowInfo in
            typePathToNode newBI typePath
                $ makeTypeNode newBI typePath {
                    kids: [
                        innerNode
                        , typeToNode (AICursor (Arrow2 md ty {-Type-} : typePath.typePath)) tyOut
                    ]
                    , tag: ArrowNodeTag
                }
        , arrow2: \typePath md tyIn {-Type-} ->
            let newBI = stepBI (Arrow2 md tyIn.ty) belowInfo in
            typePathToNode newBI typePath
                $ makeTypeNode newBI typePath {
                    kids: [
                        typeToNode (AICursor (Arrow1 md {-Type-} ty : typePath.typePath)) tyIn
                        , innerNode
                    ]
                    , tag: ArrowNodeTag
                }
        }
      )
      typePath

--typePathToNode belowInfo path@(tooth : teeth) innerNode = hole
--    case tooth of
--        Let4 md tbind tbinds def {-type-} body bodyTy ->
--            let mdctx' = hole in
--            let innerNode' = makeTypeNode {
--                dat : hole
--                , kids : [
--                    termBindToNode (AICursor (Let1 md {-tbind-} tbinds def ty body bodyTy : teeth)) tbind
--                    , termToNode (AICursor (Let3 md tbind tbinds (bIGetTerm belowInfo) body bodyTy : teeth))
--                        {ctxs, mdty: defaultMDType, ty: ty, term: def}
--                    , innerNode
--                    , termToNode (AICursor (Let5 md tbind tbinds def (bIGetTerm belowInfo) bodyTy : teeth))
--                        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
--                ]
--            } in termPathToNode (BITerm (Let md tbind tbinds def (bIGetTerm belowInfo) body bodyTy)) {ctxs, mdty: getParentMDType teeth, ty : ty, termPath: teeth} innerNode'
--        _ -> hole
constructorPathToNode :: AllContext -> BelowInfo Constructor Unit -> UpPath -> Node -> Node
constructorPathToNode ctxs belowInfo up innerNode = (hole' "constructorPathToNode")

ctrParamPathToNode :: AllContext -> BelowInfo CtrParam Unit -> UpPath -> Node -> Node
ctrParamPathToNode ctxs belowInfo up innerNode = (hole' "ctrParamPathToNode")

typeArgPathToNode :: AllContext -> BelowInfo TypeArg Unit -> UpPath -> Node -> Node
typeArgPathToNode ctxs belowInfo up innerNode = (hole' "typeArgPathToNode")

typeBindPathToNode :: AllContext -> BelowInfo TypeBind Unit -> UpPath -> Node -> Node
typeBindPathToNode ctxs belowInfo up innerNode = (hole' "typeBindPathToNode")

--typePathToNode :: BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
--typePathToNode _ { typePath: Nil } node = node
--
--typePathToNode belowInfo typePath innerNode =

termBindPathToNode :: TermBindPathRecValue -> Node -> Node
termBindPathToNode { termBindPath: Nil } innerNode = innerNode
termBindPathToNode termBindPath innerNode =
  let
    tBind = termBindPath.tBind
  in
    recTermBindPath
      { lambda1:
          \termPath md argTy body bodyTy ->
            let newBI = BITerm in -- (stepBI (Lambda1 md argTy.ty body.term bodyTy) BITerm) in
            termPathToNode newBI termPath
              $ makeTermNode newBI termPath {
                kids: [
                    innerNode
                    , typeToNode (AICursor (Lambda2 md tBind body.term bodyTy : termPath.termPath)) argTy
                    , termToNode (AICursor (Lambda3 md tBind argTy.ty bodyTy : termPath.termPath)) body
                ]
                , tag: LambdaNodeTag
              }
      , let1:
          \termPath md tyBinds def defTy body bodyTy ->
            let newBI = BITerm in -- (stepBI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) BITerm) in
            termPathToNode newBI termPath
--                $ hole' "termPathBindToNode"
              $ makeTermNode newBI termPath {
                    kids: [ innerNode
                    , typeBindListToNode (AICursor (Let2 md tBind {-List TypeBind-} def.term defTy.ty body.term bodyTy : termPath.termPath)) tyBinds
                    , termToNode (AICursor ((Let3 md tBind tyBinds.tyBinds defTy.ty body.term bodyTy) : termPath.termPath)) def
                    , typeToNode (AICursor ((Let4 md tBind tyBinds.tyBinds def.term body.term bodyTy) : termPath.termPath)) defTy
                    , termToNode (AICursor ((Let5 md tBind tyBinds.tyBinds def.term defTy.ty bodyTy) : termPath.termPath)) body
                    ]
                    , tag: LetNodeTag
              }
      , constructor1:
          \ctrPath md ctrParams ->
            constructorPathToNode ctrPath.ctxs (stepBI (Constructor1 md ctrParams.ctrParams) BITerm) ctrPath.ctrPath
                $ hole' "termPathBindToNode"
--              $ makeNode' {}
      }
      termBindPath

-- recTermBindPath
--   ?a
--   {ctxs, tBind: ?a, termBindPath: up}
ctrListPathToNode :: BelowInfo (List Constructor) Unit -> ListCtrPathRecValue -> Node -> Node
ctrListPathToNode belowInfo listCtrPath innerNode = (hole' "ctrListPathToNode")

ctrParamListPathToNode :: BelowInfo (List CtrParam) Unit -> ListCtrParamPathRecValue -> Node -> Node
ctrParamListPathToNode belowInfo listCtrParamPath innerNode = (hole' "ctrParamListPathToNode")

typeArgListPathToNode :: BelowInfo (List TypeArg) Unit -> ListTypeArgPathRecValue -> Node -> Node
typeArgListPathToNode belowInfo listTypeArgPath innerNode = (hole' "typeArgListPathToNode")

typeBindListPathToNode :: BelowInfo (List TypeBind) Unit -> ListTypeBindPathRecValue -> Node -> Node
typeBindListPathToNode belowInfo typeBindListPath innerNode =
    let tyBinds = typeBindListPath.tyBinds in
    recListTypeBindPath ({
        data2 : \termPath md tyBind ctrs body bodyTy -> hole' "typeBindListPathToNode"
        , tLet2 : \termPath md tyBind def body bodyTy -> hole' "typeBindListPathToNode"
        , typeBindListCons2 : \listTypeBindPath tyBind -> hole' "typeBindListPathToNode"
        , let2 : \termPath md tBind def defTy body bodyTy ->
              let newBI = BITerm in
              termPathToNode newBI termPath
                $ makeTermNode newBI termPath
                    { kids:
                        [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds def.term defTy.ty body.term bodyTy : termPath.termPath)) tBind
                        , innerNode
                        , termToNode (AICursor (Let3 md tBind.tBind tyBinds {-Term-} defTy.ty body.term bodyTy : termPath.termPath)) def
                        , typeToNode (AICursor (Let4 md tBind.tBind tyBinds def.term {-Type-} body.term bodyTy : termPath.termPath)) defTy
                        , termToNode (AICursor (Let5 md tBind.tBind tyBinds def.term defTy.ty {-Term-} bodyTy : termPath.termPath)) body
                        ]
                    , tag: LetNodeTag
                    }
    }) typeBindListPath

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
