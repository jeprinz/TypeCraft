module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)

import Data.Array (foldr)
import Data.Array as Array
import Data.List (List(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple.Nested ((/\))
import TypeCraft.Purescript.ChangePath (chTermPath)
import TypeCraft.Purescript.ChangeTerm (chTerm)
import TypeCraft.Purescript.Grammar (freshHole)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeQueryInsertBotNodeStyle, makeQueryInsertTopStyle, makeQueryInvalidNodeStyle, makeQueryMetaholeNodeStyle, makeQueryReplaceNewNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeCompletions, setNodeQueryString, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeArgListPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), State, getCompletion)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), ctrListToNode, ctrParamListToNode, termBindToNode, termToNode, typeArgListToNode, typeBindListToNode, typeBindToNode, typeToNode)
import TypeCraft.Purescript.Util (fromJust, hole')

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
  cursorModePathToNode
    if not (String.null cursorMode.query.string) then
      -- if the query has content
      flip (foldr ($))
        [ setNodeQueryString cursorMode.query.string
        , setNodeCompletions
            ( (Array.range 0 (n_completionGroups - 1) `Array.zip` cursorMode.query.completionGroups)
                <#> \(completionGroup_i /\ cmpls) ->
                    completionToNode false
                      if completionGroup_i == cursorMode.query.completionGroup_i `mod` n_completionGroups then
                        fromJust $ cmpls Array.!! cursorMode.query.completionGroup_i `mod` n_completionGroups
                      else
                        -- cmpls should never be empty, because then there wouldn't be a completionGroup for it
                        fromJust $ cmpls Array.!! 0
            )
        ] case getCompletion cursorMode.query of
        Nothing -> cursorModeTermToNode unit
        Just cmpl -> completionToNode true cmpl
    else
      -- if the query is empty
      cursorModeTermToNode unit
  where
  n_completionGroups = Array.length cursorMode.query.completionGroups

  cursorModePathToNode :: Node -> Node
  cursorModePathToNode = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath term -> termPathToNode (BISelect Nil term ctxs ty) { ctxs, term, termPath, ty }
    TypeCursor ctxs typePath ty -> typePathToNode BITerm { ctxs, ty, typePath }
    TypeBindCursor ctxs upPath tyBind -> typeBindPathToNode ctxs BITerm upPath
    TermBindCursor ctxs termBindPath tBind -> termBindPathToNode { ctxs, tBind, termBindPath }
    TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListPathToNode BITerm { ctxs, listTypeArgPath, tyArgs } -- BITerm upPath
    CtrListCursor ctxs listCtrPath ctrs -> ctrListPathToNode BITerm { ctxs, ctrs, listCtrPath }
    CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListPathToNode BITerm { ctxs, ctrParams, listCtrParamPath }
    TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListPathToNode BITerm { ctxs, tyBinds, listTypeBindPath }

  cursorModeTermToNode :: Unit -> Node
  cursorModeTermToNode _ =
    setNodeStyle makeCursorNodeStyle case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath term -> termToNode (AISelect termPath ctxs (term /\ ty) Nil) { ctxs, term, ty }
      TypeCursor ctxs typePath ty -> typeToNode (AICursor typePath) { ctxs, ty }
      TypeBindCursor ctxs upPath tyBind -> typeBindToNode (AICursor upPath) { ctxs, tyBind }
      TermBindCursor ctxs termBindPath tBind -> termBindToNode (AICursor termBindPath) { ctxs, tBind }
      TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListToNode (AICursor listTypeArgPath) { ctxs, tyArgs }
      CtrListCursor ctxs listCtrPath ctrs -> ctrListToNode (AICursor listCtrPath) { ctxs, ctrs }
      CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListToNode (AICursor listCtrParamPath) { ctxs, ctrParams }
      TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListToNode (AICursor listTypeBindPath) { ctxs, tyBinds }

  completionToNode :: Boolean -> Completion -> Node
  completionToNode isInline cmpl = case cmpl of
    CompletionTerm term ty -> case cursorMode.cursorLocation of
      TermCursor ctxs _ty termPath _ ->
        setNodeStyle makeQueryReplaceNewNodeStyle
          $ termToNode
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
      _ -> hole' "completionToNode CompletionTerm non-TermCursor"
    CompletionTermPath termPath ch -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath' term ->
        let
          _ /\ term' = chTerm Map.empty Map.empty ch term
        in
          -- TODO: why doesn't termPathToNode need to use termPath'? or, its wrong
          setNodeStyle makeQueryInsertTopStyle
            $ termPathToNode
                BITerm
                { ctxs, term, termPath, ty }
                ( setNodeStyle makeQueryInsertBotNodeStyle
                    if isInline then
                      -- if inline, render with cursor term at head
                      termToNode
                        (AISelect (termPath' <> termPath) ctxs (term' /\ ty) Nil)
                        { ctxs, term: term', ty }
                    else
                      -- if not inline, then render with metahole at head
                      makeMetahole unit
                )
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
