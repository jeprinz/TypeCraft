module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)
import Data.List (List(..))
import TypeCraft.Purescript.Context (defaultMDType, emptyAllContext)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), termPathToNode, typePathToNode)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), State)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), termToNode, typeToNode)
import TypeCraft.Purescript.Util (hole)

stateToNode :: State -> Node
stateToNode st = case st.mode of
  CursorMode cursor -> case cursor.cursorLocation of
    TermCursor ctxs mdty ty termPath term ->
      termPathToNode
        BITerm
        { ctxs, mdty, term, termPath, ty }
        $ setNodeStyle makeCursorNodeStyle
        $ termToNode (AICursor termPath) { ctxs, mdty, term, ty }
    TypeCursor ctxs mdty typePath ty ->
      typePathToNode
        BITerm
        { ctxs, mdty, ty, typePath }
        $ setNodeStyle makeCursorNodeStyle
        $ typeToNode (AICursor typePath) { ctxs, mdty, ty }
    TypeBindCursor ctxs mbty upPath tyBnd -> hole
    TermBindCursor ctxs mbty upPath tmBnd -> hole
    TypeArgListCursor ctxs mbty upPath tyArg -> hole
    CtrListCursor ctxs mbty upPath ctr -> hole
    CtrParamListCursor ctxs mbty upPath ctrPrm -> hole
    TypeBindListCursor ctxs mbty upPath tyBnds -> hole
  SelectMode select -> case select of
    -- need more info about root to render it
    TermSelect ctxs mdty isRootAtTop ty typePath path term ->
      typePathToNode
        (BISelect path ty unit)
        { ctxs: emptyAllContext, mdty: defaultMDType, ty: hole, typePath: Nil }
        $ setNodeStyle makeSelectTopNodeStyle
        $ typePathToNode
            BITerm
            { ctxs, mdty, ty, typePath }
        $ setNodeStyle makeSelectBotNodeStyle
        $ typeToNode (AISelect typePath path) { ctxs, mdty, ty }
    _ -> hole -- TODO: all the other selections...
