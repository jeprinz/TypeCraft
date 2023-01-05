module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)
import Data.List (List(..))
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), termPathToNode, typePathToNode)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), State)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), termToNode, typeToNode)
import TypeCraft.Purescript.Util (hole')

stateToNode :: State -> Node
stateToNode st = case st.mode of
  -- TODO: impl query
  CursorMode cursor -> case cursor.cursorLocation of
    TermCursor ctxs ty termPath term ->
      termPathToNode
        (BISelect Nil term ty)
        { ctxs, term, termPath, ty }
        $ setNodeStyle makeCursorNodeStyle
        $ termToNode (AISelect termPath Nil) { ctxs, term, ty }
    TypeCursor ctxs typePath ty ->
      typePathToNode
        (BISelect Nil ty unit)
        { ctxs, ty, typePath }
        $ setNodeStyle makeCursorNodeStyle
        $ typeToNode (AISelect typePath Nil) { ctxs, ty }
    TypeBindCursor ctxs upPath tyBnd -> hole' "stateToNode"
    TermBindCursor ctxs upPath tmBnd -> hole' "stateToNode"
    TypeArgListCursor ctxs upPath tyArg -> hole' "stateToNode"
    CtrListCursor ctxs upPath ctr -> hole' "stateToNode"
    CtrParamListCursor ctxs upPath ctrPrm -> hole' "stateToNode"
    TypeBindListCursor ctxs upPath tyBnds -> hole' "stateToNode"
  SelectMode select -> case select of
    -- need more info about root to render it
    TermSelect ctxs isRootAtTop ty topPath middlePath term -> -- NOTE: I fixed this section, it was wrong in many ways
      termPathToNode
        BITerm
        { ctxs : hole' "stateToNode", ty: hole' "stateToNode", term: hole' "stateToNode", termPath: topPath } -- TODO: we need to get the context between the middle and top path. We could either store in the state, let pathToNode compute it, or write a separate function using the termPathRec recursor which computes the context at the top of a path, and apply that to middlepath. Same with ty, and also same with term.
        $ setNodeStyle makeSelectTopNodeStyle
        $ termPathToNode
            BITerm
            { ctxs, ty, term: term, termPath: middlePath}
        $ setNodeStyle makeSelectBotNodeStyle
        $ typeToNode (AICursor (middlePath <> topPath)) { ctxs, ty }
    _ -> hole' "stateToNode" -- TODO: all the other selections...