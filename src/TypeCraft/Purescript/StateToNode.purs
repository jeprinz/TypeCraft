module TypeCraft.Purescript.StateToNode where

import Prelude
import Prim hiding (Type)

import Data.Array (foldr)
import Data.Array as Array
import Data.Int (toNumber)
import Data.List (List(..), reverse)
import Data.Maybe (Maybe(..), maybe)
import Data.String as String
import Data.Tuple (snd)
import Data.Map as Map
import Data.Tuple.Nested ((/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Alpha (applySubType)
import TypeCraft.Purescript.Dentist (downPathToCtxChange)
import TypeCraft.Purescript.Grammar (freshHole)
import TypeCraft.Purescript.ModifyState (modifyQuery, submitQuery)
import TypeCraft.Purescript.Node (Node, NodeStyle(..), NodeTag(..), addNodeStyle, makeWrapperNode, setNodeCompletions, setNodeGetCursor, setNodeQueryString)
import TypeCraft.Purescript.PathToNode (BelowInfo(..), ctrListPathToNode, ctrParamListPathToNode, termBindPathToNode, termPathToNode, typeBindListPathToNode, typeBindPathToNode, typePathToNode, insideHolePathToNode)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Mode(..), Select(..), SelectMode, State, getCompletion)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), ctrListToNode, ctrParamListToNode, termBindToNode, termToNode, typeBindListToNode, typeBindToNode, typeToNode, insideHoleToNode)
import TypeCraft.Purescript.TypeChangeAlgebra (getAllEndpoints)
import TypeCraft.Purescript.Util (fromJust', hole')
import Debug (trace)
import TypeCraft.Purescript.Alpha (subTerm)

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
  SelectMode selectMode -> selectModeToNode selectMode

selectModeToNode :: SelectMode -> Node
selectModeToNode selectMode =
  makeWrapperNode SelectModeWrapperNodeTag
    $ case selectMode.select of
        -- TODO: need more info about root to render it
        TermSelect topPath ctx1 ty1 term1 middlePath ctx2 ty2 term2 _root ->  -- TODO: render something differently depending on root?
          termPathToNode true Nil BITerm
            { ctxs: ctx1, ty: ty1, term: term1, termPath: topPath }
            $ addNodeStyle (NodeStyle "select-top")
            $ termPathToNode true topPath BITerm
                { ctxs: ctx2, ty: ty2, term: term2, termPath: middlePath }
            $ addNodeStyle (NodeStyle "select-bot")
            $ termToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ty: ty2, term: term2 }
        TypeSelect topPath ctx1 ty1 middlePath ctx2 ty2 _root ->
          typePathToNode true Nil BITerm
            { ctxs: ctx1, ty: ty1, typePath: topPath }
            $ addNodeStyle (NodeStyle "select-top")
            $ typePathToNode true topPath BITerm
                { ctxs: ctx2, ty: ty2, typePath: middlePath }
            $ addNodeStyle (NodeStyle "select-bot")
            $ typeToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ty: ty2 }
        CtrListSelect topPath ctx1 ctrs1 middlePath ctx2 ctrs2 _root ->
          ctrListPathToNode true Nil BITerm
            { ctxs: ctx1, ctrs: ctrs1, listCtrPath: topPath }
            $ addNodeStyle (NodeStyle "select-top")
            $ ctrListPathToNode true topPath BITerm
                { ctxs: ctx2, ctrs: ctrs2, listCtrPath: middlePath }
            $ addNodeStyle (NodeStyle "select-bot")
            $ ctrListToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ctrs: ctrs2 }
        CtrParamListSelect topPath ctx1 ctrParams1 middlePath ctx2 ctrParams2 _root ->
          ctrParamListPathToNode true Nil BITerm
            { ctxs: ctx1, ctrParams: ctrParams1, listCtrParamPath: topPath }
            $ addNodeStyle (NodeStyle "select-top")
            $ ctrParamListPathToNode true topPath BITerm
                { ctxs: ctx2, ctrParams: ctrParams2, listCtrParamPath: middlePath }
            $ addNodeStyle (NodeStyle "select-bot")
            $ ctrParamListToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, ctrParams: ctrParams2 }
        TypeBindListSelect topPath ctx1 tyBinds1 middlePath ctx2 tyBinds2 _root ->
          typeBindListPathToNode true Nil BITerm
            { ctxs: ctx1, tyBinds: tyBinds1, listTypeBindPath: topPath }
            $ addNodeStyle (NodeStyle "select-top")
            $ typeBindListPathToNode true topPath BITerm
                { ctxs: ctx2, tyBinds: tyBinds2, listTypeBindPath: middlePath }
            $ addNodeStyle (NodeStyle "select-bot")
            $ typeBindListToNode true (AICursor (middlePath <> topPath)) { ctxs: ctx2, tyBinds: tyBinds2 }

cursorModeToNode :: CursorMode -> Node
cursorModeToNode cursorMode =
  makeWrapperNode CursorModeWrapperNodeTag
    $ cursorModePathToNode
        if not (String.null cursorMode.query.string) then
          -- if the query has content
          flip (foldr ($))
            [ setNodeQueryString cursorMode.query.string
            , setNodeCompletions
                ( (Array.range 0 (n_completionGroups - 1) `Array.zip` cursorMode.query.completionGroups)
                    <#> \(completionGroup_j /\ cmpls) ->
                        if completionGroup_j == completionGroup_i then
                          let
                            completionGroupItem_i' = fromJust' "cursorModeToNode: completionGroupItem_i == Nothing" completionGroupItem_i
                          in
                            completionToNode { isInline: false, completionIndex: { completionGroup_i, completionGroupItem_i: completionGroupItem_i' } }
                              $ fromJust' "cursorModeToNode: cmpls Array.!! cursorMode.query.completionGroupItem_i `mod` Array.length cmpls"
                              $ (cmpls Array.!! completionGroupItem_i')
                        else
                          -- cmpls should never be empty, because then there
                          -- wouldn't be a completionGroup for it
                          completionToNode { isInline: false, completionIndex: { completionGroup_i: completionGroup_j, completionGroupItem_i: 0 } }
                            $ fromJust' "cursorModeToNode: cmpls Array.!! 0"
                            $ (cmpls Array.!! 0)
                )
                (toNumber completionGroup_i)
            ] case getCompletion cursorMode.query of
            Nothing -> cursorModeTermToNode unit
            Just cmpl ->
              let
                completionGroupItem_i' = fromJust' "cursorModeToNode: completionGroupItem_i == Nothing" completionGroupItem_i
              in
                completionToNode { isInline: true, completionIndex: { completionGroup_i, completionGroupItem_i: completionGroupItem_i' } } cmpl
        else
          -- if the query is empty
          cursorModeTermToNode unit
  where
  n_completionGroups = Array.length cursorMode.query.completionGroups

  completionGroup_i = cursorMode.query.completionGroup_i `mod` n_completionGroups

  completionGroup_active = cursorMode.query.completionGroups Array.!! completionGroup_i

  -- completionGroupItem_i cmpls = cursorMode.query.completionGroupItem_i `mod` Array.length cmpls
  completionGroupItem_i = (cursorMode.query.completionGroupItem_i `mod` _) <<< Array.length <$> completionGroup_active

  cursorModePathToNode :: Node -> Node
  cursorModePathToNode = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath term ->
        trace ("Rendering cursor mode. term is: "<> show term) \_ ->
        termPathToNode true Nil (BISelect Nil term ctxs ty) { ctxs, term, termPath, ty }
    TypeCursor ctxs typePath ty -> typePathToNode true Nil (BISelect Nil ty ctxs unit) { ctxs, ty, typePath }
    TypeBindCursor ctxs typeBindPath tyBind -> typeBindPathToNode true Nil { ctxs, typeBindPath, tyBind }
    TermBindCursor ctxs termBindPath tBind -> termBindPathToNode true Nil { ctxs, tBind, termBindPath }
    --    TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListPathToNode true Nil BITerm { ctxs, listTypeArgPath, tyArgs } -- BITerm upPath
    CtrListCursor ctxs listCtrPath ctrs -> ctrListPathToNode true Nil (BISelect Nil ctrs ctxs unit) { ctxs, ctrs, listCtrPath }
    CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListPathToNode true Nil (BISelect Nil ctrParams ctxs unit) { ctxs, ctrParams, listCtrParamPath }
    TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListPathToNode true Nil (BISelect Nil tyBinds ctxs unit) { ctxs, tyBinds, listTypeBindPath }
--insideHolePathToNode :: Boolean -> UpPath -> BelowInfo Unit Unit -> InsideHolePathRecValue -> Node -> Node
    InsideHoleCursor ctxs ty insideHolePath -> insideHolePathToNode true Nil BITerm {ctxs, ty, insideHolePath}

  cursorModeTermToNode :: Unit -> Node
  cursorModeTermToNode _ =
    addNodeStyle (NodeStyle "cursor") case cursorMode.cursorLocation of
      TermCursor ctxs ty termPath term -> termToNode true (AISelect termPath ctxs (term /\ ty) Nil) { ctxs, term, ty }
      TypeCursor ctxs typePath ty -> typeToNode true (AISelect typePath ctxs ty Nil) { ctxs, ty }
      TypeBindCursor ctxs upPath tyBind -> typeBindToNode true (AICursor upPath) { ctxs, tyBind }
      TermBindCursor ctxs termBindPath tBind -> termBindToNode true (AICursor termBindPath) { ctxs, tBind }
      --      TypeArgListCursor ctxs listTypeArgPath tyArgs -> typeArgListToNode true (AICursor listTypeArgPath) { ctxs, tyArgs }
      CtrListCursor ctxs listCtrPath ctrs -> ctrListToNode true (AISelect listCtrPath ctxs ctrs Nil) { ctxs, ctrs }
      CtrParamListCursor ctxs listCtrParamPath ctrParams -> ctrParamListToNode true (AISelect listCtrParamPath ctxs ctrParams Nil) { ctxs, ctrParams }
      TypeBindListCursor ctxs listTypeBindPath tyBinds -> typeBindListToNode true (AISelect listTypeBindPath ctxs tyBinds Nil) { ctxs, tyBinds }
      InsideHoleCursor ctxs ty insideHolePath -> insideHoleToNode true (AICursor insideHolePath) {ctxs, ty}

  completionToNode ::
    { isInline :: Boolean
    , completionIndex :: { completionGroup_i :: Int, completionGroupItem_i :: Int }
    } ->
    Completion -> Node
  completionToNode opts cmpl =
    let
      getCursor =
        Just \st ->
          maybe st identity do
            st' <- modifyQuery (_ { completionGroup_i = opts.completionIndex.completionGroup_i, completionGroupItem_i = opts.completionIndex.completionGroup_i }) st
            submitQuery st'
    in
      case cmpl of
        -- a CompletionTerm can be filled in only at InsideHoleCursor
        CompletionTerm termPre {-ty-} sub -> case cursorMode.cursorLocation of
          InsideHoleCursor ctxs tyPre _path ->
            let
              ty = applySubType sub tyPre
              term = subTerm sub termPre
            in
              setNodeGetCursor getCursor
                $ addNodeStyle (NodeStyle "query-replace-new")
                $ termToNode false
                    AINothing -- (AISelect termPath ctxs (term /\ ty) Nil)
                    { ctxs, term, ty }
          -- TODO: old, since now you can only do this at InsideHoleCursor
          -- TermCursor ctxs ty' _termPath _ ->
          --   let
          --     ty = applySubType sub ty'
          --   in
          --     setNodeGetCursor getCursor
          --       $ addNodeStyle (NodeStyle "query-replace-new")
          --       $ termToNode false
          --           AINothing -- (AISelect termPath ctxs (term /\ ty) Nil)
          --           { ctxs, term, ty }
          _ -> hole' "completionToNode CompletionTerm non-TermCursor"
        CompletionTermPath termPath _ch sub -> case cursorMode.cursorLocation of
          TermCursor ctxs tyPreSub _termPath' termPreSub ->
            let
              term = subTerm sub termPreSub -- we need to do this sub or else the types might be wrong when we try to render the path!
              ty = applySubType sub tyPreSub
              chCtxs = downPathToCtxChange ctxs (reverse termPath)
              newCtxs = snd (getAllEndpoints chCtxs)
            in
              setNodeGetCursor getCursor
                $ addNodeStyle (NodeStyle "query-insert-top")
                $ termPathToNode false Nil BITerm -- ideally we shouldn't have to specify Nil and BITerm here, as they are irrelevant. See refactors.
                    { ctxs: newCtxs {-TODO: Jacob note: this is where it needs newCtxs-}, term, termPath, ty }
                    ( addNodeStyle (NodeStyle "query-insert-bot")
                        if opts.isInline then
                          -- if inline, render with cursor term at head
                          termToNode false -- TODO: shouldn't this be false? Why should you be able to click on the query?
                            AINothing -- (AISelect (termPath' <> termPath) ctxs (term /\ ty) Nil)
                            { ctxs, term, ty }
                        else
                          -- if not inline, then render with metahole at head
                          makeMetahole unit
                    )
          _ -> hole' "completionToNode CompletionPath non-TermCursor"
        -- CompletionTermPath2 termPath newState -> case newState unit of
        --   TermCursor ctxs ty _termPath' term ->
        --       setNodeGetCursor getCursor
        --         $ addNodeStyle (NodeStyle "query-insert-top")
        --         $ termPathToNode false Nil BITerm -- ideally we shouldn't have to specify Nil and BITerm here, as they are irrelevant. See refactors.
        --             { ctxs, term, termPath, ty }
        --             ( addNodeStyle (NodeStyle "query-insert-bot")
        --                 if opts.isInline then
        --                   -- if inline, render with cursor term at head
        --                   termToNode false -- TODO: shouldn't this be false? Why should you be able to click on the query?
        --                     AINothing -- (AISelect (termPath' <> termPath) ctxs (term /\ ty) Nil)
        --                     { ctxs, term, ty }
        --                 else
        --                   -- if not inline, then render with metahole at head
        --                   makeMetahole unit
        --             )
          _ -> hole' "completionToNode CompletionPath non-TermCursor"
        CompletionType ty _sub -> case cursorMode.cursorLocation of
          TypeCursor ctxs _path _ty ->
            setNodeGetCursor getCursor
              $ addNodeStyle (NodeStyle "query-replace-new")
              $ typeToNode false
                  AINothing -- (AISelect path ctxs ty Nil)
                  { ctxs, ty }
          _ -> hole' "completionToNode CompletionType non-TypeCursor"
        CompletionTypePath path' _ch -> case cursorMode.cursorLocation of
          TypeCursor ctxs _path ty ->
            setNodeGetCursor getCursor
              $ addNodeStyle (NodeStyle "query-insert-top")
              $ typePathToNode false Nil BITerm -- ideally we shouldn't have to specify Nil and BITerm here, as they are irrelevant. See refactors.
                  { ctxs, ty, typePath: path' }
                  ( addNodeStyle (NodeStyle "query-insert-bot")
                      if opts.isInline then
                        -- if inline, render with cursor type at head
                        typeToNode false
                          AINothing -- (AISelect (path' <> path) ctxs ty (path' <> path))
                          { ctxs, ty }
                      else
                        makeMetahole unit
                  )
          _ -> unsafeThrow "completionToNode CompletionTypePath non-TypeCursor"
        CompletionCtrParamListPath path' _ch -> case cursorMode.cursorLocation of
          CtrParamListCursor ctxs _path ctrParams ->
            setNodeGetCursor getCursor
              $ addNodeStyle (NodeStyle "query-insert-top")
              $ ctrParamListPathToNode false Nil BITerm
                  { ctxs, ctrParams, listCtrParamPath: path' }
                  ( addNodeStyle (NodeStyle "query-insert-bot")
                      if opts.isInline then
                        -- if inline, render with cursor type at head
                        ctrParamListToNode false
                          AINothing -- (AISelect (path' <> path) ctxs ctrParams (path' <> path))
                          { ctxs, ctrParams }
                      else
                        addNodeStyle (NodeStyle "query-metahole")
                          $ ctrParamListToNode false
                              AINothing -- (AISelect path ctxs ctrParams Nil)
                              { ctxs, ctrParams }
                  )
          _ -> unsafeThrow "Shouldn't get here: non-CtrParamListCursor, but tried a CtrParamListPath completion!"
        CompletionCtrListPath path' _listCtrCh -> case cursorMode.cursorLocation of
          CtrListCursor ctxs _path ctrs ->
            setNodeGetCursor getCursor
              $ addNodeStyle (NodeStyle "query-insert-top")
              $ ctrListPathToNode false Nil BITerm
                  { ctxs, ctrs, listCtrPath: path' }
                  ( addNodeStyle (NodeStyle "query-insert-bot")
                      $ if opts.isInline then
                          ctrListToNode false
                            AINothing -- (AISelect (path' <> path) ctxs ctrs (path' <> path)) 
                            { ctxs, ctrs }
                        else
                          addNodeStyle (NodeStyle "query-metahole")
                            $ ctrListToNode false
                                AINothing -- (AISelect path ctxs ctrs Nil)
                                { ctxs, ctrs }
                  )
          _ -> unsafeThrow "Shouldn't get here: non-CtrListCursor, but tried a CtrPath completion!"
        CompletionTypeBindListPath path' _listTyBindCh -> case cursorMode.cursorLocation of
          TypeBindListCursor ctxs _path tyBinds ->
            setNodeGetCursor getCursor
              $ addNodeStyle (NodeStyle "query-insert-top")
              $ typeBindListPathToNode false Nil BITerm { ctxs, tyBinds, listTypeBindPath: path' }
                  ( addNodeStyle (NodeStyle "query-insert-bot")
                      if opts.isInline then
                        typeBindListToNode false AINothing { ctxs, tyBinds }
                      else
                        addNodeStyle (NodeStyle "query-metahole")
                          $ typeBindListToNode false
                              AINothing -- (AISelect (path' <> path) ctxs tyBinds Nil) 
                              { ctxs, tyBinds }
                  )
          _ -> unsafeThrow "Shouldn't get here: non-TypeBindListCursor, but tried a TypeBindList completion!"

  makeMetahole :: Unit -> Node
  makeMetahole _ = case cursorMode.cursorLocation of
    TermCursor ctxs ty termPath _ ->
      let
        term = freshHole unit
      in
        addNodeStyle (NodeStyle "query-metahole")
          $ termToNode false
              (AISelect termPath ctxs (term /\ ty) Nil)
              { ctxs, term, ty }
    TypeCursor ctxs path ty ->
      addNodeStyle (NodeStyle "query-metahole")
        $ typeToNode false
            (AISelect path ctxs ty Nil)
            { ctxs, ty }
    _ -> hole' "makeMetahole: unhandled cursor case"
