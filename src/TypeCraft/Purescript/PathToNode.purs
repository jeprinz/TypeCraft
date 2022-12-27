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

toothToDat :: Tooth -> MDTermContext -> MDTypeContext -> MDType -> NodeData
toothToDat (Let2 md _ _ _ _) mdkctx mdctx mdty = makeNodeData {indentation: hole, isParenthesized: mdty.onLeftOfApp, label: "Let"}
toothToDat tooth mdkctx mdctx mdty = hole

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

termPathToNode :: BelowInfo Term -> TermPathRecValue -> Node -> Node
termPathToNode _ {termPath: Nil} node = node
termPathToNode belowInfo pathRecVal@{termPath: tooth : _} innerNode =
    let kids' = recTermPath ({
          let2 : \down md tbind tbinds ty {-def-} body -> [
            typeToNode hole ty
            , termPathToNode hole down innerNode
            , termToNode hole body
          ]
        , let4 : \down md tbind tbinds ty def {-body-} -> hole
        , data3 : \down md tbind tbinds ctrs {-body-} -> hole
    }) in
    let kids = kids' pathRecVal in
    makeNode {
            dat: toothToDat tooth pathRecVal.mdkctx pathRecVal.mdctx pathRecVal.mdty
            , kids : [kids]
            , getCursor : Just \_ -> initState $ initCursorMode $ hole
            , getSelect : hole
            , style : makeNormalNodeStyle
    }


---- The MDType is for the top of the path (which is the end of the list)
--termPathToNode :: MDContext -> BelowInfo Term -> TermPathRecValue -> UpPath -> (MDType -> Node -> Node)
--termPathToNode _ _ _ Nil _ node = node
--termPathToNode mdctx belowInfo pathRecVal path@(tooth : teeth) mdType innerNode =
--    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
--        dat: partialNode.dat
--        , kids : [partialNode.kids]
--        , getCursor :
--            let belowTerm = case belowInfo of
--                                 BITerm term -> term
--                                 BISelect middlePath term -> combineDownPathTerm middlePath term
--            in Just \_ -> initState $ initCursorMode $ TermCursor pathRecVal.kctx pathRecVal.ctx pathRecVal.ty path belowTerm
--        , getSelect : hole
--        , style : hole
--    } in
--    recTermPath ({
--          let2 : \upRecVal md tbind tbinds {-def-} ty body bodyTy ->
--            let mdctx' = hole in -- the ctx above the let, with the variable removed
--            let innerNode' = makeNode' {
--                dat : makeNodeData {indentation : if md.bodyIndented then Just mdctx.indentation else Nothing, isParenthesized: mdType.onLeftOfApp, label: "Let"}
--                , kids: []
--              } in termPathToNode mdctx' (stepBI hole belowInfo) upRecVal teeth ?h ?h
--        , let4 : \upRecVal md tbind tbinds def defTy {-body-} bodyTy -> hole
--        , data3 : \upRecVal md tbind tbinds ctrs {-body-} bodyTy -> hole
--    }) pathRecVal tooth
--
--typePathToNode :: MDContext -> BelowInfo Type -> TypeContext -> TermContext -> Type -> UpPath -> Node -> Node
--typePathToNode _ _ _ _ _ Nil node = node
--typePathToNode mdctx belowInfo kctx ctx ty path@(tooth : teeth) innerNode =
--    let makeNode' partialNode = makeNode { -- specialize a version of makeNode with the pieces that will be the same for each case
--        dat: partialNode.dat
--        , kids : [partialNode.kids]
--        , getCursor :
--            let belowTerm = case belowInfo of
--                                 BITerm term -> term
--                                 BISelect middlePath term -> hole -- combineDownPathTerm middlePath term
--            in Just \_ -> initState $ initCursorMode $ TypeCursor kctx ctx path belowTerm
--        , getSelect : hole
--        , style : hole
--    } in
--    case tooth of
--        Let3 md tbind tbinds def {-type-} body bodyTy ->
--            let mdctx' = hole in
--            let innerNode' = makeNode' {
--                dat : hole
--                , kids : [
--                    termToNode mdctx' defaultMDType (AICursor (Let2 md tbind tbinds (bIGetTerm belowInfo) body bodyTy : teeth))
--                        {kctx, ctx, ty, term: def}
--                    , innerNode
--                    , termToNode mdctx' defaultMDType (AICursor (Let4 md tbind tbinds def (bIGetTerm belowInfo) bodyTy : teeth))
--                        {kctx, ctx, ty, term: body}
--                ]
--            } in hole -- termPathToNode mdctx' defaultMDType (BITerm (Let md tbind tbinds def (bIGetTerm belowInfo) body bodyTy)) {kctx, ctx, ty} teeth innerNode'
--        _ -> hole
