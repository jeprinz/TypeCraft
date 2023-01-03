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


data AboveInfo = AICursor UpPath | AISelect UpPath UpPath -- top path, then middle path

stepAI :: Tooth -> AboveInfo -> AboveInfo
stepAI tooth (AICursor path) = AICursor (tooth : path)
stepAI tooth (AISelect topPath middlePath) = AISelect topPath (tooth : middlePath)

aIOnlyCursor :: AboveInfo -> AboveInfo
aIOnlyCursor (AICursor path) = AICursor path
aIOnlyCursor (AISelect topPath middlePath) = AICursor (middlePath <> topPath)

aIGetPath :: AboveInfo -> UpPath
aIGetPath (AICursor path) = path
aIGetPath (AISelect top middle) = middle <> top

--type AboveInfo -- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: AboveInfo -> TermRecValue -> Node
termToNode aboveInfo term =
    let partialNode' = recTerm ({
      lambda : \md tBind ty body bodyTy ->
        {
            dat : {isParenthesized: term.mdty.onLeftOfApp, tag: makeLambdaNodeTag}
            , kids: [
                    termBindToNode (stepAI (Lambda1 md ty.ty body.term bodyTy) (aIOnlyCursor aboveInfo)) tBind
                    , typeToNode (stepAI (Lambda2 md tBind.tBind body.term bodyTy) (aIOnlyCursor aboveInfo)) ty
                    , termToNode (stepAI (Lambda3 md tBind.tBind ty.ty bodyTy) aboveInfo) body
                ]
        }
    , app : \md t1 t2 argTy outTy ->
        {
            dat : {isParenthesized: term.mdty.onRightOfApp, tag: makeAppNodeTag} -- TODO: seems like there will be some redundancy in parenthesization logic?
            , kids: [
                termToNode (stepAI (App1 md t2.term argTy outTy) aboveInfo) t1
                , termToNode (stepAI (App2 md t2.term argTy outTy) aboveInfo) t2
            ]
        }
    , var : \md x targs -> hole
    , lett : \md tBind tyBinds def defTy body bodyTy ->
        {
            dat : {isParenthesized: term.mdty.onLeftOfApp, tag: makeLetNodeTag}
            , kids: [
--                and the termBind
                termToNode (stepAI (Let2 md tBind.tBind tyBinds.tyBinds defTy.ty body.term bodyTy) aboveInfo) def
                , typeToNode (stepAI (Let3 md tBind.tBind tyBinds.tyBinds def.term body.term bodyTy) (aIOnlyCursor aboveInfo)) defTy
                , termToNode (stepAI (Let4 md tBind.tBind tyBinds.tyBinds def.term defTy.ty bodyTy) aboveInfo) body
            ]
        }
    , dataa : \md x tbinds ctrs body bodyTy -> hole
    , tlet : \md x tbinds def body bodyTy -> hole
    , typeBoundary : \md c t -> hole
    , contextBoundary : \md x c t -> hole
    , hole : \md -> hole
    , buffer : \md def defTy body bodyTy -> hole
    }) -- term
    in let partialNode = partialNode' term in
    -- pieces that are the same for every syntactic form are done here:
    makeNode {
--            dat: makeNodeData (partialNode.dat{indentation= if term.mdty.indented then makeIndentNodeIndentation else makeInlineNodeIndentation})
            dat: makeNodeData {isParenthesized: partialNode.dat.isParenthesized, label: Nothing, tag: partialNode.dat.tag,
               indentation: if term.mdty.indented then makeIndentNodeIndentation else makeInlineNodeIndentation}
            , kids : [partialNode.kids]
            , getCursor : Just \_ -> initState $ initCursorMode $ TermCursor term.ctxs term.mdty term.ty (aIGetPath aboveInfo) term.term
            , getSelect : case aboveInfo of
                     AICursor path -> Nothing
                     AISelect top middle -> Just \_ -> initState $ SelectMode $ TermSelect term.ctxs hole false term.ty middle top term.term
    }

typeToNode :: AboveInfo -> TypeRecValue -> Node
typeToNode aboveInfo ty
    = let partialNode' = recType ({
        arrow: \md ty1 ty2 -> {
            dat : {isParenthesized: ty.mdty.onLeftOfArrow, tag: makeArrowNodeTag}
            , kids: [typeToNode (stepAI (Arrow1 md ty2.ty) aboveInfo) ty1
                    , typeToNode (stepAI (Arrow2 md ty1.ty) aboveInfo) ty2]
        }
        , tHole: \md x -> {
            dat : {isParenthesized: false, tag: makeTHoleNodeTag}
            , kids: []
        }
        , tNeu: \md x tyArgs -> {
            dat : {isParenthesized: ty.mdty.onLeftOfArrow, tag: makeTNeuNodeTag}
            , kids: [] -- TODO: Put type parameters
        }
    }) in let partialNode = partialNode' ty
    in makeNode {
        dat: makeNodeData {isParenthesized: partialNode.dat.isParenthesized, label: Nothing, tag: partialNode.dat.tag,
               indentation: if ty.mdty.indented then makeIndentNodeIndentation else makeInlineNodeIndentation}
        , kids : [partialNode.kids]
        , getCursor : Just \_ -> initState $ initCursorMode $ TypeCursor ty.ctxs hole (aIGetPath aboveInfo) ty.ty
        , getSelect : case aboveInfo of
                 AICursor path -> Nothing
                 AISelect top middle -> Just \_ -> initState $ SelectMode $ TypeSelect ty.ctxs hole false top middle ty.ty
    }

ctrListToNode :: AboveInfo -> ListCtrRecValue -> Node
ctrListToNode aboveInfo ctrs = hole

ctrToNode :: AboveInfo -> Constructor -> Node
ctrToNode aboveInfo ctr = hole

--ctrParamToNode :: AllContext -> AboveInfo -> UpPath -> CtrParam -> Node
--ctrParamToNode ctxs aboveInfo up (CtrParam md ty) = makeNode {
--    dat: makeNodeData {indentation: hole, isParenthesized: false, label: "CtrParam"}
--    , kids: [[typeToNode (stepAI (CtrParam1 md) (aIOnlyCursor aboveInfo)) {ctxs, ty}]]
--    , getCursor: Nothing
--    , getSelect: Nothing
--    , style: makeNormalNodeStyle
--}

typeArgToNode :: AboveInfo -> TypeArgRecValue -> Node
typeArgToNode aboveInfo tyArg = hole

typeBindToNode :: AboveInfo -> TypeBindRecValue -> Node
typeBindToNode aboveInfo tyBind = hole

termBindToNode :: AboveInfo -> TermBindRecValue -> Node
termBindToNode aboveInfo {ctxs, tBind: tBind@(TermBind md x)} = makeNode {
    dat : makeNodeData {indentation: hole, isParenthesized: false, label: Nothing, tag: makeTermBindNodeTag}
    , kids: []
    , getCursor : Just \_ -> initState $ initCursorMode $ TermBindCursor ctxs hole (aIGetPath aboveInfo) tBind
    , getSelect: Nothing
}

ctrParamListToNode :: AboveInfo -> ListCtrParamRecValue -> Node
ctrParamListToNode aboveInfo ctrParams = hole

typeArgListToNode :: AboveInfo -> ListTypeArgRecValue -> Node
typeArgListToNode aboveInfo tyArgs = hole

-----------------------------------------------------------------------------------------------------------