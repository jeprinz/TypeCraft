module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)

import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Debug (trace)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, DownPath, Term, TermBind, Tooth(..), Type, TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.Node (Node, NodeTag(..), makeNode, setCalculatedNodeData)
import TypeCraft.Purescript.PathRec (TermPathRecValue, TypePathRecValue, TermBindPathRecValue, recTermBindPath, recTermPath, recTypePath)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode, makeState)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), termBindToNode, termToNode, typeToNode)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermToNode (typeBindListToNode)

data BelowInfo term ty
  = BITerm
  | BISelect DownPath term ty -- middle path, then bottom term. ty is type of term.

--stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
----stepBI tooth (BITerm syn) = BITerm (step syn)
----stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
--stepBI = hole
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!
stepBI :: forall syn synty. Tooth -> BelowInfo syn synty -> BelowInfo syn synty
stepBI tooth BITerm = BITerm

stepBI tooth (BISelect middle bottom ty) = BISelect (tooth : middle) bottom ty

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
              BISelect middlePath term ty -> Just \_ -> makeState $ SelectMode $ TermSelect termPath.ctxs true ty termPath.termPath middlePath term
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
                        , typeBindListToNode (AICursor (Let2 md tBind.tBind {-List TypeBind-} term ty.ty body.term bodyTy : termPath.termPath)) tyBinds
                        , innerNode
                        , typeToNode (AICursor (Let4 md tBind.tBind tyBinds.tyBinds term {-Type-} body.term bodyTy : upRecVal.termPath)) ty
                        , termToNode (AICursor (Let5 md tBind.tBind tyBinds.tyBinds term ty.ty {-Term-} bodyTy : upRecVal.termPath)) body
                        ]
                    }
        , app1: \upRecVal md {-Term-} t2 argTy bodyTy -> hole' "termPathToNode"
        , app2: \upRecVal md t1 {-Term-} argTy bodyTy -> hole' "termPathToNode"
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
                            [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds.tyBinds term ty.ty def.term bodyTy : upRecVal.termPath)) tBind
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
                BISelect middlePath term _ -> typePath.ty -- TODO: combineDownPathTerm middlePath term
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
              let newBI = (stepBI (Lambda2 md tBind.tBind body.term bodyTy) BITerm) in
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
              let newBI = (stepBI (Let4 md tBind.tBind tyBinds.tyBinds def.term body.term bodyTy) BITerm) in
              termPathToNode newBI termPath
                $ makeTermNode newBI termPath
                    { kids:
                        [ termBindToNode (AICursor (Let1 md {-tbind-} tyBinds.tyBinds def.term typePath.ty body.term bodyTy : termPath.termPath)) tBind
                        , typeBindListToNode (AICursor (Let2 md tBind.tBind {-List TypeBind-} def.term ty body.term bodyTy : termPath.termPath)) tyBinds
                        , innerNode
                        , termToNode (AICursor (Let3 md tBind.tBind tyBinds.tyBinds {-Term-} typePath.ty body.term bodyTy : termPath.termPath)) def
                        , termToNode (AICursor (Let5 md tBind.tBind tyBinds.tyBinds def.term typePath.ty {-Term-} bodyTy : termPath.termPath)) body
                        ]
                    , tag: LambdaNodeTag
                    }
        , buffer2: \termPath md def {-Type-} body bodyTy -> (hole' "typePathToNode")
        , tLet3: \termPath md tyBind tyBinds {-Type-} body bodyTy -> (hole' "typePathToNode")
        , ctrParam1: \ctrParamPath md {-Type-} -> (hole' "typePathToNode")
        , typeArg1: \typeArgPath md {-Type-} -> (hole' "typePathToNode")
        , arrow1: \typePath md tyIn {-Type-} -> (hole' "typePathToNode")
        , arrow2: \typePath md {-Type-} tyOut -> (hole' "typePathToNode")
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

-- TODO: I'm not sure if I'm using BITerm correctly, but since a `BelowInfo _ _`
-- is not provided to `termBindPathToNode` then I need to use something as the
-- bottom when I do `stepBI ...`
termBindPathToNode :: TermBindPathRecValue -> Node -> Node
termBindPathToNode { termBindPath: Nil } innerNode = innerNode

termBindPathToNode termBindPath innerNode =
  let
    tBind = termBindPath.tBind
  in
    recTermBindPath
      { lambda1:
          \termPath md argTy body bodyTy ->
          trace ("termBindPathToNode.lambda1.termPath.termPath = " <> show termPath.termPath) \_ ->
            let newBI = (stepBI (Lambda1 md argTy.ty body.term bodyTy) BITerm) in
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
            let newBI = (stepBI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) BITerm) in
            termPathToNode newBI termPath
                $ hole' "termPathBindToNode"
              $ makeTermNode newBI termPath {
                    kids: [ innerNode
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
ctrListPathToNode :: AllContext -> BelowInfo (List Constructor) Unit -> UpPath -> Node -> Node
ctrListPathToNode ctxs belowInfo up innerNode = (hole' "ctrListPathToNode")

ctrParamListPathToNode :: AllContext -> BelowInfo (List CtrParam) Unit -> UpPath -> Node -> Node
ctrParamListPathToNode ctxs belowInfo up innerNode = (hole' "ctrParamListPathToNode")

typeArgListPathToNode :: AllContext -> BelowInfo (List TypeArg) Unit -> UpPath -> Node -> Node
typeArgListPathToNode ctxs belowInfo up innerNode = (hole' "typeArgListPathToNode")

typeBindListPathToNode :: AllContext -> BelowInfo (List TypeBind) Unit -> UpPath -> Node -> Node
typeBindListPathToNode ctxs belowInfo up innerNode = (hole' "typeBindListPathToNode")

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
