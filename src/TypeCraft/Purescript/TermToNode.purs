module TypeCraft.Purescript.TermToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec

import Data.List (List, (:))
import Data.Map.Internal (Map(..), empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Util (hole)


data AboveInfo = AICursor DownPath | AISelect DownPath DownPath -- top path, then middle path

stepAI :: Tooth -> AboveInfo -> AboveInfo
stepAI tooth (AICursor path) = AICursor (tooth : path)
stepAI tooth (AISelect topPath middlePath) = AISelect topPath (tooth : middlePath)

aIOnlyCursor :: AboveInfo -> AboveInfo
aIOnlyCursor (AICursor path) = AICursor path
aIOnlyCursor (AISelect topPath middlePath) = AICursor (topPath <> middlePath)

aIGetPath :: AboveInfo -> DownPath
aIGetPath (AICursor path) = path
aIGetPath (AISelect top middle) = top <> middle

--type AboveInfo -- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: AboveInfo -> TermRecValue -> Node
termToNode aboveInfo term =
    let partialNode' = recTerm ({
      lambda : \md tbind@(TermBind {varName} x) ty body ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onLeftOfApp, label: "Lambda"}
            , kids: [
--                    termBindToNode term.kctx term.ctx (stepAI (Lambda1 md ty.ty body.term) (aIOnlyCursor aboveInfo)) tbind
                    typeToNode (stepAI (Lambda2 md tbind body.term) (aIOnlyCursor aboveInfo)) ty
                    , termToNode (stepAI (Lambda3 md tbind ty.ty) aboveInfo) body
                ]
        }
    , app : \md t1 t2 argTy ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onRightOfApp, label: "App"} -- TODO: seems like there will be some redundancy in parenthesization logic?
            , kids: [
                termToNode (stepAI (App1 md t2.term argTy) aboveInfo) t1
                , termToNode (stepAI (App2 md t2.term argTy) aboveInfo) t2
            ]
        }
    , var : \md x targs -> hole
    , lett : \md tbind@(TermBind {varName} x) tbinds def defTy body ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onLeftOfApp, label: "Let"}
            , kids: [
--                and the termBind
                termToNode (stepAI (Let2 md tbind tbinds defTy.ty body.term) aboveInfo) def
                , typeToNode (stepAI (Let3 md tbind tbinds def.term body.term) (aIOnlyCursor aboveInfo)) defTy
                , termToNode (stepAI (Let4 md tbind tbinds def.term defTy.ty) aboveInfo) body
            ]
        }
    , dataa : \md x tbinds ctrs body -> hole
    , tlet : \md x tbinds def body -> hole
    , typeBoundary : \md c t -> hole
    , contextBoundary : \md x c t -> hole
    , hole : \md -> hole
    , buffer : \md def defTy body -> hole
    }) -- term
    in let partialNode = partialNode' term in
    -- pieces that are the same for every syntactic form are done here:
    makeNode {
            dat: partialNode.dat
            , kids : [partialNode.kids]
            , getCursor : Just \_ -> initState $ initCursorMode $ TermCursor (aIGetPath aboveInfo) term.term
            , getSelect : hole
            , style : hole
    }

typeToNode :: AboveInfo -> TypeRecValue -> Node
typeToNode aboveInfo {kctx, ctx, ty}
    = let partialNode = case ty of
            Arrow md ty1 ty2 -> hole
            THole md x -> hole
            TNeu md x targs -> hole
    in makeNode {
        dat: partialNode.dat
        , kids : partialNode.kids
        , getCursor : 
            if partialNode.isCursorable
                then Just \_ -> initState $ initCursorMode $ TypeCursor hole ty -- Isn't this the same for every case?
                else Nothing
        , getSelect: 
            if partialNode.isSelectable
                then Just hole
                else Nothing
        , style : partialNode.style
    }

ctrListToNode :: MDContext -> DownPath -> TypeContext -> TermContext -> List Constructor -> Node
ctrListToNode mdctx up kctx ctx ctrs = hole

ctrToNode :: MDContext -> DownPath -> TypeContext -> TermContext -> Constructor -> Node
ctrToNode mdctx up kctx ctx ctr = hole

ctrParamToNode :: MDContext -> DownPath -> TypeContext -> TermContext -> CtrParam -> Node
ctrParamToNode mdctx up kctx ctx param = hole

termBindToNode :: MDContext -> TypeContext -> TermContext -> AboveInfo -> TermBind -> Node
termBindToNode mdctx kctx ctx aboveInfo tbind@(TermBind md x) = makeNode {
    dat : makeNodeData {indentation: hole, isParenthesized: false, label: "TypeBind"}
    , kids: []
    , getCursor : Just \_ -> initState $ initCursorMode $ TermBindCursor (aIGetPath aboveInfo) tbind
    , getSelect: Nothing
    , style: makeNormalNodeStyle
}
