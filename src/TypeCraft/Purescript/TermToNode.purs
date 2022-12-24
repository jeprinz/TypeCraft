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
import Data.Functor (map)

type MDContext = {
    indentation :: Int,
    termVarNames :: Map TermVarID String,
    typeVarNames :: Map TypeVarID String
}

--type PathInfo -- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: MDContext -> UpPath -> UpPath -> TermRecValue -> Node
termToNode mdctx aboveTerm intoTerm term =
    let partialNode' = recTerm ({
      lambda : \md tbind@(TermBind {varName} x) ty body ->
        let mdctx' = mdctx {termVarNames = insert x varName mdctx.termVarNames} in -- TODO: something something indentation
        {
            dat : makeNodeData {indentation : if md.bodyIndented then Just mdctx.indentation else Nothing, isParenthesized: false, label: "lambda"}
            , kids: [
                    termToNode mdctx' aboveTerm (Lambda3 md tbind ty.ty : intoTerm) body
                    , typeToNode mdctx' (Lambda2 md tbind body.term : (aboveTerm <> intoTerm)) hole ty
                ]
        }
    , app : \md t1 t2 argTy outTy -> hole
    , var : \md x targs -> hole
    , lett : \md tbind@(TermBind {varName} x) tbinds def defTy body bodyTy ->
        let mdctx' = mdctx {termVarNames = insert x varName mdctx.termVarNames} in
        {
            dat : makeNodeData {indentation : hole, isParenthesized: false, label: "let"}
            , kids: [
--                and the termBind
                termToNode mdctx' aboveTerm (Let1 md tbind tbinds defTy.ty body.term bodyTy : intoTerm) def
--                and the type
                , termToNode mdctx' aboveTerm (Let3 md tbind tbinds def.term defTy.ty bodyTy : intoTerm) body
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
            dat: partialNode.dat
            , kids : [partialNode.kids]
            , getCursor :
                if true
                    then Just \_ -> initState $ initCursorMode $ TermCursor term.kctx term.ctx term.ty (aboveTerm <> intoTerm) term.term -- Isn't this the same for every case?
                    else Nothing
            , getSelect : hole
            , style : hole
    }

typeToNode :: MDContext -> UpPath -> UpPath -> TypeRecValue -> Node
typeToNode mdctx above into {kctx, ctx, ty}
    = let partialNode = case ty of
            Arrow md ty1 ty2 -> hole
            THole md x -> hole
            TNeu md x targs -> hole
    in makeNode {
        dat: partialNode.dat
        , kids : partialNode.kids
        , getCursor : 
            if partialNode.isCursorable
                then Just \_ -> initState $ initCursorMode $ TypeCursor kctx ctx hole ty -- Isn't this the same for every case?
                else Nothing
        , getSelect: 
            if partialNode.isSelectable
                then Just hole
                else Nothing
        , style : partialNode.style
    }

ctrListToNode :: MDContext -> UpPath -> TypeContext -> TermContext -> List Constructor -> Node
ctrListToNode mdctx up kctx ctx ctrs = hole

ctrToNode :: MDContext -> UpPath -> TypeContext -> TermContext -> Constructor -> Node
ctrToNode mdctx up kctx ctx ctr = hole

ctrParamToNode :: MDContext -> UpPath -> TypeContext -> TermContext -> CtrParam -> Node
ctrParamToNode mdctx up kctx ctx param = hole
