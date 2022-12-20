module TypeCraft.Purescript.TermToNode where

import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.TermRec
import TypeCraft.Purescript.Node
import Prim hiding (Type)
import TypeCraft.Purescript.Util (hole)

import Prelude
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.State

type MDContext = {
    indentation :: Int
}

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: MDContext -> TermPath -> TermRecValue -> Node
termToNode mdctx up term = recTerm
    {
      lambda : \md tbind ty body ->
        let mdctx' = mdctx in -- TODO: add name of variable!
        makeNode {
            dat : makeNodeDataSane {indentation : mdctx.indentation, isParenthesized: false, label: "lambda"}
            , kids : [[termToNode mdctx' (Lambda2 up md tbind ty.ty) body]]
            , getCursor : \_ -> TermCursor term.kctx term.ctx term.ty up term.term -- Isn't this the same for every case?
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
}
    term
