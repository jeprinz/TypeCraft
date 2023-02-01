module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)
import Data.Array (foldr)
import Data.Array as Array
import Data.Int (toNumber)
import Data.List (List(..), reverse)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple.Nested ((/\))
import TypeCraft.Purescript.Grammar (freshHole)
import TypeCraft.Purescript.Node (Node, makeCursorNodeStyle, makeQueryInsertBotNodeStyle, makeQueryInsertTopStyle, makeQueryMetaholeNodeStyle, makeQueryReplaceNewNodeStyle, makeSelectBotNodeStyle, makeSelectTopNodeStyle, setNodeCompletions, setNodeQueryString, setNodeStyle)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeArgListPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), State, getCompletion)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), ctrListToNode, ctrParamListToNode, termBindToNode, termToNode, typeArgListToNode, typeBindListToNode, typeBindToNode, typeToNode)
import TypeCraft.Purescript.Unification (applySubType)
import TypeCraft.Purescript.Util (fromJust', hole')
import TypeCraft.Purescript.Dentist (downPathToCtxChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.TypeChangeAlgebra (getAllEndpoints)
import TypeCraft.Purescript.Util (hole)
import Effect.Exception.Unsafe (unsafeThrow)

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
      termPathToNode true Nil BITerm
        { ctxs: ctx1, ty: ty1, term: term1, termPath: topPath }
        $ setNodeStyle makeSelectTopNodeStyle
        $ termPathToNode true topPath BITerm
            { ctxs: ctx2, ty: ty2, term: term2, termPath: middlePath }
        $ setNodeStyle makeSelectBotNodeStyle
        $ termToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ty: ty2, term: term2 }
    { select: TypeSelect topPath ctx1 ty1 middlePath ctx2 ty2 root } ->
      typePathToNode true Nil BITerm
        { ctxs: ctx1, ty: ty1, typePath: topPath}
        $ setNodeStyle makeSelectTopNodeStyle
        $ typePathToNode true topPath BITerm
            {ctxs: ctx2, ty: ty2, typePath: middlePath}
        $ setNodeStyle makeSelectBotNodeStyle
        $ typeToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ty: ty2}

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
                <#> \(completionGroup_j /\ cmpls) ->
                    if completionGroup_j == completionGroup_i then
                      completionToNode { isInline: false }
                        $ fromJust' "cursorModeToNode: cmpls Array.!! cursorMode.query.completionGroupItem_i `mod` Array.length cmpls"
                        $ cmpls
                        Array.!! completionGroupItem_i cmpls
                    else
                      -- cmpls should never be empty, because then there
                      -- wouldn't be a completionGroup for it
                      completionToNode { isInline: false }
                        $ fromJust' "cursorModeToNode: cmpls Array.!! 0"
                        $ cmpls
                        Array.!! 0
            )
            (toNumber completionGroup_i)
        ] case getCompletion cursorMode.query of
        Nothing -> cursorModeTermToNode unit
        Just cmpl -> completionToNode { isInline: true } cmpl
    else
      -- if the query is empty
      cursorModeTermToNode unit
  where
  n_completionGroups = Array.length cursorMode.query.completionGroups

  completionGroup_i = cursorMode.query.completionGroup_i `mod` n_completionGroups

  completionGroupItem_i cmpls = cursorMode.query.completionGroupItem_i `mod` Array.length cmpls

  cursorModePathToNode :: Node -> Node
  cursorModePathToNode = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath term -> termPathToNode true Nil (BISelect Nil term ctxs ty) { ctxs, term, termPath, ty }
    TypeCursor ctxs typePath ty -> typePathToNode true Nil (BISelect Nil ty ctxs unit) { ctxs, ty, typePath }
    TypeBindCursor ctxs typeBindPath tyBind -> typeBindPathToNode true Nil {ctxs, typeBindPath, tyBind}
    TermBindCursor ctxs termBindPath tBind -> termBindPathToNode true Nil { ctxs, tBind, termBindPath }
--    TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListPathToNode true Nil BITerm { ctxs, listTypeArgPath, tyArgs } -- BITerm upPath
    CtrListCursor ctxs listCtrPath ctrs -> ctrListPathToNode true Nil BITerm { ctxs, ctrs, listCtrPath }
    CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListPathToNode true Nil BITerm { ctxs, ctrParams, listCtrParamPath }
    TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListPathToNode true Nil BITerm { ctxs, tyBinds, listTypeBindPath }

  cursorModeTermToNode :: Unit -> Node
  cursorModeTermToNode _ =
    setNodeStyle makeCursorNodeStyle case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath term -> termToNode true (AISelect termPath ctxs (term /\ ty) Nil) { ctxs, term, ty }
      TypeCursor ctxs typePath ty -> typeToNode true (AISelect typePath ctxs ty Nil) { ctxs, ty }
      TypeBindCursor ctxs upPath tyBind -> typeBindToNode true (AICursor upPath) { ctxs, tyBind }
      TermBindCursor ctxs termBindPath tBind -> termBindToNode true (AICursor termBindPath) { ctxs, tBind }
--      TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListToNode true (AICursor listTypeArgPath) { ctxs, tyArgs }
      CtrListCursor ctxs listCtrPath ctrs -> ctrListToNode true (AICursor listCtrPath) { ctxs, ctrs }
      CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListToNode true (AICursor listCtrParamPath) { ctxs, ctrParams }
      TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListToNode true (AICursor listTypeBindPath) { ctxs, tyBinds }

  completionToNode :: { isInline :: Boolean } -> Completion -> Node
  completionToNode opts cmpl = case cmpl of
    CompletionTerm term {-ty-} sub -> case cursorMode.cursorLocation of
      TermCursor ctxs ty' termPath _ ->
        let
          ty = applySubType sub ty'
        in
          setNodeStyle makeQueryReplaceNewNodeStyle
            $ termToNode false
                (AISelect termPath ctxs (term /\ ty) Nil)
                { ctxs, term, ty }
      _ -> hole' "completionToNode CompletionTerm non-TermCursor"
    CompletionTermPath termPath ch -> case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath' term ->
        let chCtxs = downPathToCtxChange ctxs (reverse termPath) in
        let newCtxs = snd (getAllEndpoints chCtxs) in
        setNodeStyle makeQueryInsertTopStyle
          $ termPathToNode false Nil BITerm -- ideally we shouldn't have to specify Nil and BITerm here, as they are irrelevant. See refactors.
              { ctxs: newCtxs {-TODO: Jacob note: this is where it needs newCtxs-}, term, termPath, ty }
              ( setNodeStyle makeQueryInsertBotNodeStyle
                  if opts.isInline then
                    -- if inline, render with cursor term at head
                    termToNode true -- TODO: shouldn't this be false? Why should you be able to click on the query?
                      (AISelect (termPath' <> termPath) ctxs (term /\ ty) Nil)
                      { ctxs, term, ty }
                  else
                    -- if not inline, then render with metahole at head
                    makeMetahole unit
              )
      _ -> hole' "completionToNode CompletionPath non-TermCursor"
    CompletionType ty _sub -> case cursorMode.cursorLocation of
      TypeCursor ctxs path _ty ->
        setNodeStyle makeQueryReplaceNewNodeStyle
          $ typeToNode false
              (AISelect path ctxs ty Nil)
              { ctxs, ty }
      _ -> hole' "completionToNode CompletionType non-TypeCursor"
    CompletionTypePath path' ch -> case cursorMode.cursorLocation of
      TypeCursor ctxs path ty ->
        setNodeStyle makeQueryInsertTopStyle
          $ typePathToNode false Nil BITerm -- ideally we shouldn't have to specify Nil and BITerm here, as they are irrelevant. See refactors.
              { ctxs, ty, typePath: path' }
              ( setNodeStyle makeQueryInsertBotNodeStyle
                  if opts.isInline then
                    -- if inline, render with cursor type at head
                    typeToNode true
                      (AISelect (path' <> path) ctxs ty (path' <> path))
                      { ctxs, ty }
                  else
                    makeMetahole unit
              )
      _ -> hole' "completionToNode CompletionTypePath non-TypeCursor"
    CompletionCtrListPath path' listCtrCh -> case cursorMode.cursorLocation of
        CtrListCursor ctxs path ctrs ->
            setNodeStyle makeQueryInsertTopStyle
              $ ctrListPathToNode false Nil BITerm
                  { ctxs, ctrs, listCtrPath: path'}
                  ( setNodeStyle makeQueryInsertBotNodeStyle
                        if opts.isInline then
                            -- if inline, render with cursor type at head
                            ctrListToNode true
                              (AISelect (path' <> path) ctxs ctrs (path' <> path))
                              { ctxs, ctrs }
                          else
                            setNodeStyle makeQueryMetaholeNodeStyle
                                $ ctrListToNode false
                                    (AISelect path ctxs ctrs Nil)
                                    {ctxs, ctrs}
                      )
        _ -> unsafeThrow "Shouldn't get here: non-CtrListCursor, but tried a CtrPath completion!"
    _ -> hole' "This type of completion hasn't been implemented yet" -- TODO: remove this message once we implemented all the completions sorts

  makeMetahole :: Unit -> Node
  makeMetahole _ = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath _ ->
      let
        term = freshHole unit
      in
        setNodeStyle makeQueryMetaholeNodeStyle
          $ termToNode false
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
    TypeCursor ctxs path ty ->
      setNodeStyle makeQueryMetaholeNodeStyle
        $ typeToNode false
            (AISelect path ctxs ty Nil)
            { ctxs, ty }
    _ -> hole' "makeMetahole: unhandled cursor case"
