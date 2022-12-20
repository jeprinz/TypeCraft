module TypeCraft.Purescript.TermToNode where

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (Map(..), empty, lookup, insert, union)
import TypeCraft.Purescript.TermRec
import TypeCraft.Purescript.Node
import Prim hiding (Type)
import TypeCraft.Purescript.Util (hole)
import Data.List (List, (:))

import Prelude
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.State

type MDContext = {
    indentation :: Int,
    termVarNames :: Map TermVarID String,
    typeVarNames :: Map TypeVarID String
}

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: MDContext -> TermPath -> TermRecValue -> Node
termToNode mdctx up term =
    let partialNode' = recTerm ({
      lambda : \md tbind@(TermBind {varName} x) ty body ->
        let mdctx' = mdctx {termVarNames = insert x varName mdctx.termVarNames} in -- TODO: something something indentation
        {
            dat : makeNodeDataSane {indentation : mdctx.indentation, isParenthesized: false, label: "lambda"}
            , kids : [[termToNode mdctx' (Lambda2 up md tbind ty.ty) body]] -- TODO: I guess we need another node for the variable name?
            , isCursorable : true
            , getSelect : hole
            , isSelectable : hole
            , style : hole
        }
    , app : \md t1 t2 argTy outTy -> hole
    , var : \md x targs -> hole
    , lett : \md x tbinds def defTy body bodyTy -> hole
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
            , kids : partialNode.kids
            , getCursor : \_ -> TermCursor term.kctx term.ctx term.ty up term.term -- Isn't this the same for every case?
            , isCursorable: partialNode.isCursorable
            , getSelect : hole
            , isSelectable : partialNode.isSelectable
            , style : partialNode.style
    }

typeToNode :: MDContext -> TypePath -> TypeContext -> TermContext -> Type -> Node
typeToNode mdctx up kctx ctx ty
    = let partialNode = case ty of
            Arrow md ty1 ty2 -> hole
            THole md x -> hole
            TNeu md x targs -> hole
    in makeNode {
        dat: partialNode.dat
        , kids : partialNode.kids
        , getCursor : \_ -> TypeCursor kctx ctx up ty -- Isn't this the same for every case?
        , isCursorable: partialNode.isCursorable
        , getSelect : hole
        , isSelectable : partialNode.isSelectable
        , style : partialNode.style
    }

ctrListToNode :: MDContext -> CtrListPath -> TypeContext -> TermContext -> List Constructor -> Node
ctrListToNode mdctx up kctx ctx ctrs = hole

ctrToNode :: MDContext -> ConstructorPath -> TypeContext -> TermContext -> Constructor -> Node
ctrToNode mdctx up kctx ctx ctr = hole

ctrParamToNode :: MDContext -> CtrParamPath -> TypeContext -> TermContext -> CtrParam -> Node
ctrParamToNode mdctx up kctx ctx param = hole
