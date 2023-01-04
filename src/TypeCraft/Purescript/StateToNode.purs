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
import TypeCraft.Purescript.PathRec (getMDType)

stateToNode :: State -> Node
stateToNode st = case st.mode of
  CursorMode cursor -> case cursor.cursorLocation of
    TermCursor ctxs mdty ty termPath term ->
      termPathToNode
        (BISelect Nil term ty)
        { ctxs, mdty, term, topmd: defaultMDType, termPath, ty }
        $ setNodeStyle makeCursorNodeStyle
        $ termToNode (AISelect termPath Nil) { ctxs, mdty, term, ty }
    TypeCursor ctxs mdty typePath ty ->
      typePathToNode
        (BISelect Nil ty unit)
        { ctxs, mdty, topmd: defaultMDType, ty, typePath }
        $ setNodeStyle makeCursorNodeStyle
        $ typeToNode (AISelect typePath Nil) { ctxs, mdty, ty }
    TypeBindCursor ctxs mbty upPath tyBnd -> hole
    TermBindCursor ctxs mbty upPath tmBnd -> hole
    TypeArgListCursor ctxs mbty upPath tyArg -> hole
    CtrListCursor ctxs mbty upPath ctr -> hole
    CtrParamListCursor ctxs mbty upPath ctrPrm -> hole
    TypeBindListCursor ctxs mbty upPath tyBnds -> hole
  SelectMode select -> case select of
    -- need more info about root to render it
    TermSelect ctxs mdty isRootAtTop ty topPath middlePath term -> -- NOTE: I fixed this section, it was wrong in many ways
      termPathToNode
        BITerm
        { ctxs : hole, mdty: defaultMDType, topmd: defaultMDType, ty: hole, term: hole, termPath: topPath } -- TODO: we need to get the context between the middle and top path. We could either store in the state, let pathToNode compute it, or write a separate function using the termPathRec recursor which computes the context at the top of a path, and apply that to middlepath. Same with ty, and also same with term.
        $ setNodeStyle makeSelectTopNodeStyle
        $ termPathToNode
            BITerm
            { ctxs, mdty, topmd: getMDType defaultMDType topPath, ty, term: term, termPath: middlePath}
        $ setNodeStyle makeSelectBotNodeStyle
        $ typeToNode (AICursor (middlePath <> topPath)) { ctxs, mdty, ty }
    _ -> hole -- TODO: all the other selections...
--{ctxs :: AllContext, mdty :: MDType, topmd :: MDType, ty :: Type, term :: Term, termPath :: UpPath}