module TypeCraft.Purescript.StateToNode where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Data.Array (foldr)
import Data.List (List(..))
import Data.String as String
import TypeCraft.Purescript.Grammar (freshHole, freshTHole)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeQueryMetaholeNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeCompletionGroups, setNodeQueryString, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeArgListPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), State)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), ctrListToNode, ctrParamListToNode, termBindToNode, termToNode, typeArgListToNode, typeBindListToNode, typeBindToNode, typeToNode)
import TypeCraft.Purescript.Util (hole')

{-
TODO: Note from Jacob: Counterintuitvely, all cursor modes should use BISelect
and AISelect, because it is from a cursor mode that a selection is possible.
Conversely, all select modes should use BITerm and AICursor, because from select
mode another selection is not possible.
-}
-- TODO: somehow `st.mode.cursorLocation` is being set to the mode
stateToNode :: State -> Node
stateToNode st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath term ->
      termPathToNode (BISelect Nil term ctxs ty) { ctxs, term, termPath, ty }
        $ encursor cursorMode
        $ termToNode (AISelect termPath ctxs (term /\ ty) Nil) { ctxs, term, ty }
    TypeCursor ctxs typePath ty ->
      typePathToNode BITerm { ctxs, ty, typePath }
        $ encursor cursorMode
        $ typeToNode (AICursor typePath) { ctxs, ty }
    TypeBindCursor ctxs upPath tyBind ->
      typeBindPathToNode ctxs BITerm upPath
        $ encursor cursorMode
        $ typeBindToNode (AICursor upPath) { ctxs, tyBind }
    TermBindCursor ctxs termBindPath tBind ->
      termBindPathToNode { ctxs, tBind, termBindPath }
        $ encursor cursorMode
        $ termBindToNode (AICursor termBindPath) { ctxs, tBind }
    TypeArgListCursor ctxs listTypeArgPath tyArgs ->
      typeArgListPathToNode BITerm { ctxs, listTypeArgPath, tyArgs } -- BITerm upPath
        $ encursor cursorMode
        $ typeArgListToNode (AICursor listTypeArgPath) { ctxs, tyArgs }
    CtrListCursor ctxs listCtrPath ctrs ->
      ctrListPathToNode BITerm { ctxs, ctrs, listCtrPath }
        $ encursor cursorMode
        $ ctrListToNode (AICursor listCtrPath) { ctxs, ctrs }
    CtrParamListCursor ctxs listCtrParamPath ctrParams ->
      ctrParamListPathToNode BITerm { ctxs, ctrParams, listCtrParamPath }
        $ encursor cursorMode
        $ ctrParamListToNode (AICursor listCtrParamPath) { ctxs, ctrParams }
    TypeBindListCursor ctxs listTypeBindPath tyBinds ->
      typeBindListPathToNode BITerm { ctxs, tyBinds, listTypeBindPath }
        $ encursor cursorMode
        $ typeBindListToNode (AICursor listTypeBindPath) { ctxs, tyBinds }
  SelectMode select -> case select of
    -- TODO: need more info about root to render it
    { select: TermSelect topPath ctx1 ty1 term1 middlePath ctx2 ty2 term2 root } ->  -- TODO: render something differently depending on root?
      termPathToNode
        BITerm
        { ctxs: ctx1, ty: ty1, term: term1, termPath: topPath }
        $ setNodeStyle makeSelectTopNodeStyle
        $ termPathToNode
            BITerm
            { ctxs: ctx2, ty: ty2, term: term2, termPath: middlePath }
        $ setNodeStyle makeSelectBotNodeStyle
        $ termToNode (AICursor (middlePath <> topPath)) { ctxs: ctx2, ty: ty2, term: term2 }
    _ -> hole' "stateToNode" -- TODO: all the other selections...

encursor :: CursorMode -> Node -> Node
encursor cursorMode =
  flip (foldr ($))
    [ setNodeStyle makeCursorNodeStyle
    , if not (String.null cursorMode.query.string) then
        flip (foldr ($))
          [ setNodeQueryString cursorMode.query.string
          , setNodeCompletionGroups
              ( ((_ `completionToNode` freshMetahole unit) <$> _)
                  <$> cursorMode.query.completionGroups
              )
          ]
      else
        identity
    ]
  where
  completionToNode :: Completion -> Node -> Node
  completionToNode cmpl node = case cmpl of
    CompletionTerm term -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath _ ->
        termToNode
          (AISelect termPath ctxs (term /\ ty) Nil)
          { ctxs, term, ty }
      _ -> hole' "completionToNode CompletionTerm non-TermCursor"
    CompletionPath termPath -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath' term ->
        termPathToNode
          (BISelect Nil term ctxs ty)
          { ctxs, term, termPath: termPath <> termPath', ty }
          node
      _ -> hole' "completionToNode CompletionPath non-TermCursor"

  freshMetahole :: Unit -> Node
  freshMetahole _ = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath _ ->
      let
        term = freshHole unit
      in
        setNodeStyle makeQueryMetaholeNodeStyle
          $ termToNode
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
    _ -> hole' "freshMetahole non-TermCursor"
