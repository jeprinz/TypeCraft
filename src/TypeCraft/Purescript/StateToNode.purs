module TypeCraft.Purescript.StateToNode where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Data.Array (foldr)
import Data.Array as Array
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import TypeCraft.Purescript.Grammar (freshHole, freshTHole)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeQueryInsertBotNodeStyle, makeQueryInsertTopStyle, makeQueryInvalidNodeStyle, makeQueryMetaholeNodeStyle, makeQueryReplaceNewNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeCompletionGroups, setNodeQueryString, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeArgListPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), State, getCompletion)
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
  CursorMode cursorMode -> cursorModeToNode cursorMode
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

cursorModeToNode :: CursorMode -> Node
cursorModeToNode cursorMode =
  if not (String.null cursorMode.query.string) then case getCompletion cursorMode.query of
    -- if the query is not empty and there are no completions
    Nothing ->
      flip (foldr ($))
        [ setNodeStyle makeQueryInvalidNodeStyle
        , setNodeQueryString cursorMode.query.string
        ]
        $ cursorModeTermToNode unit
    -- if the query is not empty and there are completions
    Just cmpl ->
      flip (foldr ($))
        [ setNodeQueryString cursorMode.query.string
        , setNodeCompletionGroups
            ( ((_ `completionToNode` false) <$> _)
                <$> cursorMode.query.completionGroups
            )
        ]
        $ completionToNode cmpl true
  else
    -- if the query is empty
    cursorModeTermToNode unit
  where
  cursorModeTermToNode :: Unit -> Node
  cursorModeTermToNode _ = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath term -> termToNode (AISelect termPath ctxs (term /\ ty) Nil) { ctxs, term, ty }
    TypeCursor ctxs typePath ty -> typeToNode (AICursor typePath) { ctxs, ty }
    TypeBindCursor ctxs upPath tyBind -> typeBindToNode (AICursor upPath) { ctxs, tyBind }
    TermBindCursor ctxs termBindPath tBind -> termBindToNode (AICursor termBindPath) { ctxs, tBind }
    TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListToNode (AICursor listTypeArgPath) { ctxs, tyArgs }
    CtrListCursor ctxs listCtrPath ctrs -> ctrListToNode (AICursor listCtrPath) { ctxs, ctrs }
    CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListToNode (AICursor listCtrParamPath) { ctxs, ctrParams }
    TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListToNode (AICursor listTypeBindPath) { ctxs, tyBinds }

  completionToNode :: Completion -> Boolean -> Node
  completionToNode cmpl isSelected = case cmpl of
    CompletionTerm term -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath _ ->
        setNodeStyle makeQueryReplaceNewNodeStyle
          $ termToNode
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
      _ -> hole' "completionToNode CompletionTerm non-TermCursor"
    CompletionPath termPath -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath' term ->
        -- TODO: why doesn't termPathToNode need to use termPath'? or, its wrong
        setNodeStyle makeQueryInsertTopStyle
          $ termPathToNode
              BITerm
              { ctxs, term, termPath, ty }
              if isSelected then
                -- if this path completion is selected, then actually render it
                -- inline with the current program, putting the current term at the
                -- head
                setNodeStyle makeQueryInsertBotNodeStyle
                  $ termToNode
                      (AISelect (termPath <> termPath') ctxs (term /\ ty) Nil)
                      { ctxs, term, ty }
              else
                -- if this path completion is not selected, the render it with a
                -- metavariable at the head
                makeMetahole unit
      _ -> hole' "completionToNode CompletionPath non-TermCursor"

  makeMetahole :: Unit -> Node
  makeMetahole _ = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath _ ->
      let
        term = freshHole unit
      in
        setNodeStyle makeQueryMetaholeNodeStyle
          $ termToNode
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
    _ -> hole' "makeMetahole non-TermCursor"
