module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeArgListPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), State)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), ctrListToNode, ctrParamListToNode, termBindToNode, termToNode, typeArgListToNode, typeBindListToNode, typeBindToNode, typeToNode)
import TypeCraft.Purescript.Util (hole')

{-
TODO: Note from Jacob:
Counterintuitvely, all cursor modes should use BISelect and AISelect, because it is from a cursor mode that a selection
is possible.
Conversely, all select modes should use BITerm and AICursor, because from select mode another selection is not possible.
-}
-- TODO: somehow `st.mode.cursorLocation` is being set to the mode
stateToNode :: State -> Node
stateToNode st = case st.mode of
  -- TODO: impl query
  CursorMode cursor -> case cursor.cursorLocation of
    TermCursor ctxs ty termPath term ->
      termPathToNode BITerm { ctxs, term, termPath, ty }
        $ setNodeStyle makeCursorNodeStyle
        $ termToNode (AICursor termPath) { ctxs, term, ty }
    TypeCursor ctxs typePath ty ->
      typePathToNode BITerm { ctxs, ty, typePath }
        $ setNodeStyle makeCursorNodeStyle
        $ typeToNode (AICursor typePath) { ctxs, ty }
    TypeBindCursor ctxs upPath tyBind ->
      typeBindPathToNode ctxs BITerm upPath
        $ setNodeStyle makeCursorNodeStyle
        $ typeBindToNode (AICursor upPath) { ctxs, tyBind }
    TermBindCursor ctxs termBindPath tBind ->
      termBindPathToNode { ctxs, tBind, termBindPath }
        $ setNodeStyle makeCursorNodeStyle
        $ termBindToNode (AICursor termBindPath) { ctxs, tBind }
    TypeArgListCursor ctxs listTypeArgPath tyArgs ->
      typeArgListPathToNode BITerm {ctxs, listTypeArgPath, tyArgs} -- BITerm upPath
        $ setNodeStyle makeCursorNodeStyle
        $ typeArgListToNode (AICursor listTypeArgPath) { ctxs, tyArgs }
    CtrListCursor ctxs listCtrPath ctrs ->
      ctrListPathToNode BITerm {ctxs, ctrs, listCtrPath}
        $ setNodeStyle makeCursorNodeStyle
        $ ctrListToNode (AICursor listCtrPath) { ctxs, ctrs }
    CtrParamListCursor ctxs listCtrParamPath ctrParams ->
      ctrParamListPathToNode BITerm {ctxs, ctrParams, listCtrParamPath}
        $ setNodeStyle makeCursorNodeStyle
        $ ctrParamListToNode (AICursor listCtrParamPath) { ctxs, ctrParams }
    TypeBindListCursor ctxs listTypeBindPath tyBinds ->
      typeBindListPathToNode BITerm {ctxs, tyBinds, listTypeBindPath}
        $ setNodeStyle makeCursorNodeStyle
        $ typeBindListToNode (AICursor listTypeBindPath) { ctxs, tyBinds }
  SelectMode select -> case select of
    -- need more info about root to render it
    TermSelect ctxs isRootAtTop ty topPath middlePath term ->  -- NOTE: I fixed this section, it was wrong in many ways
      termPathToNode
        BITerm
        { ctxs: hole' "stateToNode", ty: hole' "stateToNode", term: hole' "stateToNode", termPath: topPath } -- TODO: we need to get the context between the middle and top path. We could either store in the state, let pathToNode compute it, or write a separate function using the termPathRec recursor which computes the context at the top of a path, and apply that to middlepath. Same with ty, and also same with term.
        $ setNodeStyle makeSelectTopNodeStyle
        $ termPathToNode
            BITerm
            { ctxs, ty, term: term, termPath: middlePath }
        $ setNodeStyle makeSelectBotNodeStyle
        $ typeToNode (AICursor (middlePath <> topPath)) { ctxs, ty }
    _ -> hole' "stateToNode" -- TODO: all the other selections...
