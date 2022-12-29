module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec

import Data.List (List(..), (:))

import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermToNode
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.Dentist

data BelowInfo term ty = BITerm term | BISelect DownPath term ty -- middle path, then bottom term. ty is type of term.

--stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
----stepBI tooth (BITerm syn) = BITerm (step syn)
----stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
--stepBI = hole
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!

stepBI :: forall syn synty . ToothAppendable syn => Tooth -> BelowInfo syn synty -> BelowInfo syn synty
stepBI tooth (BITerm term) = BITerm (toothAppend tooth term)
stepBI tooth (BISelect middle bottom ty) = BISelect (tooth : middle) bottom ty

--bIOnlyCursor :: BelowInfo -> BelowInfo

bIGetTerm :: forall term ty. ToothAppendable term => BelowInfo term ty -> term
bIGetTerm (BITerm t) = t
bIGetTerm (BISelect path t ty) = teethAppend path t

-- The MDType is for the top of the path (which is the end of the list)
termPathToNode :: BelowInfo Term Type -> TermPathRecValue -> (Node -> Node)
termPathToNode _ {termPath: Nil} node = node
termPathToNode belowInfo termPath innerNode =
    let mdty = getMDType termPath.termPath in
    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
        dat: partialNode.dat
        , kids : [partialNode.kids]
        , getCursor :
            let belowTerm = case belowInfo of
                 BITerm term -> term
                 BISelect middlePath term ty -> combineDownPathTerm middlePath term
            in Just \_ -> initState $ initCursorMode $ TermCursor termPath.ctxs mdty termPath.ty termPath.termPath belowTerm
        , getSelect : case belowInfo of
                 BITerm term -> Nothing
                 BISelect middlePath term ty -> Just \_ -> initState $ SelectMode $ TermSelect termPath.ctxs ty true termPath.termPath middlePath term
        , style : hole
    } in
    recTermPath ({
          let2 : \upRecVal md tbind tbinds {-def-} ty body bodyTy ->
            let mdctx' = hole in -- the ctx above the let, with the variable removed
            let innerNode' = makeNode' {
                dat : makeNodeData {indentation : hole, isParenthesized: mdty.onLeftOfApp, label: "Let"}
                , kids: [
                    termBindToNode termPath.ctxs (AICursor (Let1 md {-tbind-} tbinds (bIGetTerm belowInfo) ty.ty body.term bodyTy : upRecVal.termPath)) tbind
                    , innerNode
                    , typeToNode (AICursor (Let3 md tbind tbinds (bIGetTerm belowInfo) {-Type-} body.term bodyTy : upRecVal.termPath)) ty
                    , termToNode (AICursor (Let4 md tbind tbinds (bIGetTerm belowInfo) ty.ty {-Term-} bodyTy : upRecVal.termPath)) body
                ]
              } in termPathToNode (stepBI hole belowInfo) upRecVal innerNode'
        , app1 : \upRecVal md {-Term-} t2 argTy bodyTy -> hole
        , app2 : \upRecVal md t1 {-Term-} argTy bodyTy -> hole
        , lambda3 : \upRecVal md tbind argTy {-body-} bodyTy -> hole
        , buffer1 : \upRecVal md {-Term-} bufTy body bodyTy -> hole
        , buffer3 : \upRecVal md buf bufTy {-Term-} bodyTy -> hole
        , typeBoundary1 : \upRecVal md change {-Term-} -> hole
        , contextBoundary1 : \upRecVal md x change {-Term-} -> hole
        , tLet4 : \upRecVal md tyBind tyBinds def {-Term-} bodyTy -> hole
        , let4 : \upRecVal md tbind tbinds def defTy {-body-} bodyTy -> hole
        , data4 : \upRecVal md tbind tbinds ctrs {-body-} bodyTy -> hole
    }) termPath

typePathToNode :: AllContext -> BelowInfo Type Unit -> UpPath -> Node -> Node
typePathToNode _ _ Nil node = node
typePathToNode ctxs belowInfo path@(tooth : teeth) innerNode =
    let ty = bIGetTerm belowInfo in
    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
        dat: partialNode.dat
        , kids : [partialNode.kids]
        , getCursor :
            let belowTerm = case belowInfo of
                                 BITerm term -> term
                                 BISelect middlePath term _ -> hole -- combineDownPathTerm middlePath term
            in Just \_ -> initState $ initCursorMode $ TypeCursor ctxs path belowTerm
        , getSelect : hole
        , style : hole
    } in
    case tooth of
        Let3 md tbind tbinds def {-type-} body bodyTy ->
            let mdctx' = hole in
            let innerNode' = makeNode' {
                dat : hole
                , kids : [
                    termBindToNode ctxs (AICursor (Let1 md {-tbind-} tbinds def ty body bodyTy : teeth)) tbind
                    , termToNode (AICursor (Let2 md tbind tbinds (bIGetTerm belowInfo) body bodyTy : teeth))
                        {ctxs, mdty: defaultMDType, ty: ty, term: def}
                    , innerNode
                    , termToNode (AICursor (Let4 md tbind tbinds def (bIGetTerm belowInfo) bodyTy : teeth))
                        {ctxs, mdty: defaultMDType, ty: bodyTy, term: body}
                ]
            } in termPathToNode (BITerm (Let md tbind tbinds def (bIGetTerm belowInfo) body bodyTy)) {ctxs, mdty: getParentMDType teeth, ty : ty, termPath: teeth} innerNode'
        _ -> hole

constructorPathToNode :: AllContext -> BelowInfo Constructor Unit -> UpPath -> Node -> Node
constructorPathToNode ctxs belowInfo up innerNode = hole

ctrParamPathToNode :: AllContext -> BelowInfo CtrParam Unit -> UpPath -> Node -> Node
ctrParamPathToNode ctxs belowInfo up innerNode = hole

typeArgPathToNode :: AllContext -> BelowInfo TypeArg Unit -> UpPath -> Node -> Node
typeArgPathToNode ctxs belowInfo up innerNode = hole

typeBindPathToNode :: AllContext -> BelowInfo TypeBind Unit -> UpPath -> Node -> Node
typeBindPathToNode ctxs belowInfo up innerNode = hole

termBindPathToNode :: AllContext -> BelowInfo TermBind Unit -> UpPath -> Node -> Node
termBindPathToNode ctxs belowInfo up innerNode = hole

ctrListPathToNode :: AllContext -> BelowInfo (List Constructor) Unit -> UpPath -> Node -> Node
ctrListPathToNode ctxs belowInfo up innerNode = hole

ctrParamListPathToNode :: AllContext -> BelowInfo (List CtrParam) Unit -> UpPath -> Node -> Node
ctrParamListPathToNode ctxs belowInfo up innerNode = hole

typeArgListToNode :: AllContext -> BelowInfo (List TypeArg) Unit -> UpPath -> Node -> Node
typeArgListToNode  ctxs belowInfo up innerNode = hole

typeBindListToNode :: AllContext -> BelowInfo (List TypeBind) Unit -> UpPath -> Node -> Node
typeBindListToNode  ctxs belowInfo up innerNode = hole

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