module TypeCraft.Purescript.TermToNode where

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
      lambda : \md tbind@(TermBind {varName} x) ty body bodyTy ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onLeftOfApp, label: "Lambda"}
            , kids: [
                    termBindToNode term.ctxs (stepAI (Lambda1 md ty.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tbind
                    , typeToNode (stepAI (Lambda2 md tbind body.term bodyTy) (aIOnlyCursor aboveInfo)) ty
                    , termToNode (stepAI (Lambda3 md tbind ty.ty bodyTy) aboveInfo) body
                ]
        }
    , app : \md t1 t2 argTy ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onRightOfApp, label: "App"} -- TODO: seems like there will be some redundancy in parenthesization logic?
            , kids: [
                termToNode (stepAI (App1 md t2.term argTy outTy) aboveInfo) t1
                , termToNode (stepAI (App2 md t2.term argTy outTy) aboveInfo) t2
            ]
        }
    , var : \md x targs -> hole
    , lett : \md tbind@(TermBind {varName} x) tbinds def defTy body bodyTy ->
        {
            dat : makeNodeData {indentation : hole, isParenthesized: term.mdty.onLeftOfApp, label: "Let"}
            , kids: [
--                and the termBind
                termToNode (stepAI (Let2 md tbind tbinds defTy.ty body.term bodyTy) aboveInfo) def
                , typeToNode (stepAI (Let3 md tbind tbinds def.term body.term bodyTy) (aIOnlyCursor aboveInfo)) defTy
                , termToNode (stepAI (Let4 md tbind tbinds def.term defTy.ty bodyTy) aboveInfo) body
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
            , getCursor : Just \_ -> initState $ initCursorMode $ TermCursor term.ctxs term.mdty term.ty (aIGetPath aboveInfo) term.term
            , getSelect : case aboveInfo of
                     AICursor path -> Nothing
                     AISelect top middle -> Just \_ -> initState $ SelectMode $ TermSelect term.ctxs term.ty false top middle term.term
            , style : hole
    }

typeToNode :: AboveInfo -> TypeRecValue -> Node
typeToNode aboveInfo {ctxs, ty}
    = let partialNode = case ty of
            Arrow md ty1 ty2 -> {
                dat: makeNodeData {indentation: hole, isParenthesized: true, label: "Arrow"}
                , kids: [
                ]
            }
            THole md x -> hole
            TNeu md x targs -> hole
    in makeNode {
        dat: partialNode.dat
        , kids : partialNode.kids
        , getCursor : Just \_ -> initState $ initCursorMode $ TypeCursor ctxs (aIGetPath aboveInfo) ty
        , getSelect : case aboveInfo of
                 AICursor path -> Nothing
                 AISelect top middle -> Just \_ -> initState $ SelectMode $ TypeSelect ctxs false top middle ty
        , style : makeNormalNodeStyle
    }

ctrListToNode :: AllContext -> AboveInfo -> UpPath -> List Constructor -> Node
ctrListToNode ctxs aboveInfo up Nil = hole
ctrListToNode ctxs aboveInfo up (ctr : ctrs) = hole

ctrToNode :: AllContext -> AboveInfo -> UpPath -> Constructor -> Node
ctrToNode ctxs aboveInfo up (Constructor md tbind ctrParams) = hole

ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
    , kids: [[typeToNode (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
    , getCursor: Nothing
    , getSelect: Nothing
    , style: makeNormalNodeStyle
}

typeArgToNode :: AllContext -> UpPath -> AboveInfo -> TypeArg -> Node
typeArgToNode ctxs aboveInfo up (TypeArg md ty) = hole

typeBindToNode :: AllContext -> AboveInfo -> TypeBind -> Node
typeBindToNode ctxs aboveInfo (TypeBind md x) = hole

termBindToNode :: AllContext -> AboveInfo -> TermBind -> Node
termBindToNode ctxs aboveInfo tbind@(TermBind md x) = makeNode {
    dat : makeNodeData {indentation: hole, isParenthesized: false, label: "TermBind"}
    , kids: []
    , getCursor : Just \_ -> initState $ initCursorMode $ TermBindCursor ctxs (aIGetPath aboveInfo) tbind
    , getSelect: Nothing
    , style: makeNormalNodeStyle
}

ctrParamListToNode :: AllContext -> AboveInfo -> UpPath -> List CtrParam -> Node
ctrParamListToNode ctxs aboveInfo up Nil = hole
ctrParamListToNode ctxs aboveInfo up (ctrParam : ctrParams) = hole

typeArgListToNode :: AllContext -> AboveInfo -> UpPath -> List TypeArg -> Node
typeArgListToNode ctxs aboveInfo up Nil = hole
typeArgListToNode ctxs aboveInfo up (tyArg : tyArgs) = hole
