module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec

import Data.List (List(..), (:))
import Data.Map.Internal (Map(..), empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermToNode
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.Dentist

data BelowInfo term = BITerm term | BISelect DownPath term -- middle path, then bottom term

--stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
----stepBI tooth (BITerm syn) = BITerm (step syn)
----stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
--stepBI = hole
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!

stepBI :: forall syn . ToothAppendable syn => Tooth -> BelowInfo syn -> BelowInfo syn
stepBI tooth (BITerm term) = BITerm (toothAppend tooth term)
stepBI tooth (BISelect middle bottom) = BISelect (tooth : middle) bottom

--bIOnlyCursor :: BelowInfo -> BelowInfo

bIGetTerm :: forall term. BelowInfo term -> term
bIGetTerm (BITerm t) = t
bIGetTerm (BISelect path t) = hole -- use a typeclass to implement a combinePathSyn "term" for each syntactic type "term". Implement these instances in Dentist.purs.

-- The MDType is for the top of the path (which is the end of the list)
termPathToNode :: BelowInfo Term -> TermPathRecValue -> (Node -> Node)
termPathToNode _ {termPath: Nil} node = node
termPathToNode belowInfo termPath innerNode =
    let mdty = getMDType termPath.termPath in
    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
        dat: partialNode.dat
        , kids : [partialNode.kids]
        , getCursor :
            let belowTerm = case belowInfo of
                                 BITerm term -> term
                                 BISelect middlePath term -> combineDownPathTerm middlePath term
            in Just \_ -> initState $ initCursorMode $ TermCursor termPath.ctxs mdty termPath.ty termPath.termPath belowTerm
        , getSelect : hole
        , style : hole
    } in
    recTermPath ({
          let2 : \upRecVal md tbind tbinds {-def-} ty body bodyTy ->
            let mdctx' = hole in -- the ctx above the let, with the variable removed
            let innerNode' = makeNode' {
                dat : makeNodeData {indentation : hole, isParenthesized: mdty.onLeftOfApp, label: "Let"}
                , kids: []
              } in termPathToNode (stepBI hole belowInfo) upRecVal innerNode
        , let4 : \upRecVal md tbind tbinds def defTy {-body-} bodyTy -> hole
        , data3 : \upRecVal md tbind tbinds ctrs {-body-} bodyTy -> hole
    }) termPath

typePathToNode :: AllContext -> BelowInfo Type -> Type -> UpPath -> Node -> Node
typePathToNode _ _ _ Nil node = node
typePathToNode ctxs belowInfo ty path@(tooth : teeth) innerNode =
    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
        dat: partialNode.dat
        , kids : [partialNode.kids]
        , getCursor :
            let belowTerm = case belowInfo of
                                 BITerm term -> term
                                 BISelect middlePath term -> hole -- combineDownPathTerm middlePath term
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
                    termToNode (AICursor (Let2 md tbind tbinds (bIGetTerm belowInfo) body bodyTy : teeth))
                        {ctxs, mdty: defaultMDType, ty, term: def}
                    , innerNode
                    , termToNode (AICursor (Let4 md tbind tbinds def (bIGetTerm belowInfo) bodyTy : teeth))
                        {ctxs, mdty: defaultMDType, ty, term: body}
                ]
            } in hole -- termPathToNode mdctx' defaultMDType (BITerm (Let md tbind tbinds def (bIGetTerm belowInfo) body bodyTy)) {kctx, ctx, ty} teeth innerNode'
        _ -> hole

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