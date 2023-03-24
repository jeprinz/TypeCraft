module TypeCraft.Purescript.ModifyState where

import Prelude
import Data.Array ((:), uncons)
import Data.Array as Array
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (snd, fst)
import Debug (trace, traceM)
import Data.Tuple.Nested ((/\))
import Debug as Debug
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Alpha (applySubType, subAllCtx, subTermPath, subInsideHolePath, subTerm)
import TypeCraft.Purescript.ChangePath (chListCtrParamPath, chListCtrPath, chListTypeBindPath, chTermPath, chTypePath)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.CursorMovement (cursorLocationToSelect, getCursorChildren, moveSelectLeft, moveSelectRight, stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.Dentist (downPathToCtxChange, termPathToChange, typeBindPathToChange, typePathToChange)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.ModifyIndentation (toggleIndentation)
import TypeCraft.Purescript.State (Clipboard(..), Completion(..), CursorLocation(..), CursorMode, Mode(..), Query, Select(..), State, botSelectOrientation, emptyQuery, getCompletion, makeCursorMode, selectToCursorLocation, topSelectOrientation)
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.Util
import TypeCraft.Purescript.SmallStep.Freshen (freshenTerm, freshenTermPath)
import TypeCraft.Purescript.Unification (runUnify, normThenUnify)
import Data.Either (Either(..))
import TypeCraft.Purescript.PathRec (recInsideHolePath)
import TypeCraft.Purescript.Alpha (convertSub)
import Data.Maybe (maybe)

handleKey :: Key -> State -> Maybe State
handleKey key st
  | key.key == "p" && (key.metaKey || key.ctrlKey) = do
    -- Debug.traceM "==[ current state.mode ]====================================="
    -- Debug.traceM $ show st
    -- Debug.traceM "============================================================="
    case st.mode of
      CursorMode { cursorLocation: TermCursor _ctxs ty path tm  } -> do
        Debug.traceM "==[ path ]====================================="
        Debug.traceM $ show path
        Debug.traceM "==[ term ]====================================="
        Debug.traceM $ show tm
        Debug.traceM "==[ type ]====================================="
        Debug.traceM $ show ty
      _ -> Nothing
    Just st

handleKey key st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TypeBindCursor ctxs path (TypeBind md tyVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TypeBindCursor ctxs path (TypeBind md { varName = varName } tyVarId) } }
    TermBindCursor ctxs path (TermBind md tmVarId)
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TermBindCursor ctxs path (TermBind md { varName = varName } tmVarId) } }
    --    CtrParamListCursor ctxs path ctrs -> hole' "handleKey CtrParamListCursor" -- Jacob Note: why was this line here? I'm not sure.
    _
      | Just query <- manipulateQuery key st cursorMode -> do
        -- not the we don't `checkpoint` here, since every little modification
        -- of the query string and selection shouldn't by undoable
        pure $ st { mode = CursorMode cursorMode { query = query } }
      | (key.ctrlKey || key.metaKey) && key.key == "z" -> undo st
      | (key.ctrlKey || key.metaKey) && key.key == "Z" -> redo st
      | key.key == "ArrowLeft" && key.shiftKey -> moveSelectPrev st
      | key.key == "ArrowRight" && key.shiftKey -> moveSelectNext st
      | key.key == "ArrowLeft" -> moveCursorPrev st
      | key.key == "ArrowRight" -> moveCursorNext st
      | key.key == "Escape" -> escape st
      | key.key == "Tab" -> do
        cursorLocation' <- toggleIndentation cursorMode.cursorLocation
        pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
      | key.key == "Enter" -> submitQuery st
      | key.key == "Backspace" -> delete st
      | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
      | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
      | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
      | otherwise -> Nothing
  SelectMode _selectMode
    | key.key == "Escape" -> escape st
    | key.key == "ArrowLeft" && key.shiftKey -> moveSelectPrev st
    | key.key == "ArrowRight" && key.shiftKey -> moveSelectNext st
    | key.key == "ArrowLeft" -> moveCursorPrev st
    | key.key == "ArrowRight" -> moveCursorNext st
    | key.key == "Backspace" -> delete st
    | key.key == "c" && (key.ctrlKey || key.metaKey) -> copy st
    | key.key == "x" && (key.ctrlKey || key.metaKey) -> cut st
    | key.key == "v" && (key.ctrlKey || key.metaKey) -> paste st
    | otherwise -> Nothing

submitQuery :: State -> Maybe State
submitQuery st = case st.mode of
  CursorMode cursorMode -> do
    compl <- getCompletion cursorMode.query
    cursorMode' <- submitCompletion cursorMode compl
    -- checkpoints the pre-submission mode with a cleared query string
    pure
      $ (checkpoint st { mode = CursorMode cursorMode { query { string = "" } } })
          { mode = CursorMode cursorMode' }
  _ -> Nothing

modifyQuery :: (Query -> Query) -> State -> Maybe State
modifyQuery f st = case st.mode of
  CursorMode cursorMode -> pure st { mode = CursorMode cursorMode { query = f cursorMode.query } }
  _ -> Nothing

submitCompletion :: CursorMode -> Completion -> Maybe CursorMode
submitCompletion cursorMode compl = case cursorMode.cursorLocation of
  InsideHoleCursor ctxs ty path -> case compl of
    CompletionTerm preTerm {-ty'-} sub ->
      let
        ty' = applySubType sub ty
        tm = subTerm sub preTerm
        path' = subInsideHolePath sub path
        ctxs' = subAllCtx sub ctxs
        termPath = case path' of
          (Hole1 _) List.: termPath -> termPath
          _ -> unsafeThrow "Shouldn't happen"
      in
        pure
          { cursorLocation: TermCursor ctxs' ty' termPath tm
          , query: emptyQuery
          }
    _ -> Nothing
  TermCursor ctxs ty path tm -> case compl of
    CompletionTerm tm' {-ty'-} sub ->
      let
        ty' = applySubType sub ty

        path' = subTermPath sub path

        ctxs' = subAllCtx sub ctxs
      in
        pure
          { cursorLocation: TermCursor ctxs' ty' path' tm'
          , query: emptyQuery
          }
    CompletionTermPath pathNew ch sub ->
      let
        path' = subTermPath sub path
        pathNew' = subTermPath sub pathNew
        ty' = applySubType sub ty
        ctxs' = subAllCtx sub ctxs
        tm' = subTerm sub tm
        (kctx' /\ ctx') /\ path'' = chTermPath ch { ctxs: ctxs', ty: ty', termPath: path', term: tm }
        tm'' = chTermBoundary kctx' ctx' (tyInject ty') tm'
        ctxs'' = ctxs' { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
        chCtxs = downPathToCtxChange ctxs'' (List.reverse pathNew')
        newCtxs = snd (getAllEndpoints chCtxs)
      in
        pure
          { cursorLocation: TermCursor newCtxs ty' (pathNew' <> path'') tm''
          , query: emptyQuery
          }
    -- CompletionTermPath2 _ newState ->
    --   pure
    --     { cursorLocation: newState unit
    --     , query: emptyQuery
    --     }
    _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty -> case compl of
    CompletionType ty' _sub ->
      --            let path' = subTypePath sub path in
      --            let ctxs' = subAllCtx sub ctxs in
      let
        (kctx' /\ ctx') /\ path' = chTypePath (Replace ty ty') { ctxs, ty, typePath: path }
      in
        let
          ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
        in
          pure
            { cursorLocation: TypeCursor ctxs' path' ty'
            , query: emptyQuery
            }
    CompletionTypePath pathNew ch ->
      let
        (kctx' /\ ctx') /\ path' = chTypePath ch { ctxs, ty: ty, typePath: path }
      in
        let
          ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
        in
          pure
            { cursorLocation: TypeCursor ctxs' (pathNew <> path') ty
            , query: emptyQuery
            }
    _ -> unsafeThrow "tried to submit a non-CompletionType* completion at a TypeCursor"
  CtrListCursor ctxs path ctrs -> case compl of
    CompletionCtrListPath pathNew ch ->
      let
        path' = chListCtrPath ch { ctxs, listCtrPath: path, ctrs }
      in
        pure
          { cursorLocation: CtrListCursor ctxs (pathNew <> path') ctrs
          , query: emptyQuery
          }
    _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  CtrParamListCursor ctxs path ctrParams -> case compl of
    CompletionCtrParamListPath pathNew ch ->
      let
        path' = chListCtrParamPath ch { ctxs, ctrParams, listCtrParamPath: path }
      in
        pure
          { cursorLocation: CtrParamListCursor ctxs (pathNew <> path') ctrParams
          , query: emptyQuery
          }
    _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  TypeBindListCursor ctxs path tyBinds -> case compl of
    CompletionTypeBindListPath pathNew ch ->
      let
        path' = chListTypeBindPath ch { ctxs, tyBinds, listTypeBindPath: path }
      in
        pure
          { cursorLocation: TypeBindListCursor ctxs (pathNew <> path') tyBinds
          , query: emptyQuery
          }
    _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  _ -> Nothing -- TODO: submit queries at other kinds of cursors?

checkpoint :: State -> State
checkpoint st = st { history = st.mode : st.history }

-- doesn't `checkpoint`
moveCursorPrev :: State -> Maybe State
moveCursorPrev st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorBackwards cursorLocation) }
  _ -> do moveCursorPrev =<< escape st

-- doesn't `checkpoint`
moveCursorNext :: State -> Maybe State
moveCursorNext st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorForwards cursorLocation) }
  _ -> moveCursorNext =<< escape st

moveSelectPrev :: State -> Maybe State
moveSelectPrev st = do
  select <- case st.mode of
    CursorMode { cursorLocation } -> cursorLocationToSelect botSelectOrientation cursorLocation
    SelectMode { select } -> pure select
  mode <- moveSelectLeft select
  pure $ st { mode = mode }

moveSelectNext :: State -> Maybe State
moveSelectNext st = do
  select <- case st.mode of
    CursorMode { cursorLocation } ->
      if (List.null (getCursorChildren cursorLocation)) then
        Nothing
      else
        cursorLocationToSelect topSelectOrientation cursorLocation
    SelectMode { select } -> pure select
  mode <- moveSelectRight select
  pure $ st { mode = mode }

setSelect :: Select -> State -> Maybe State
setSelect select st = pure $ st { mode = SelectMode { select } }

requireCursorMode :: State -> Maybe CursorMode
requireCursorMode st = case st.mode of
  CursorMode cursorMode -> pure cursorMode
  _ -> Nothing

undo :: State -> Maybe State
undo st = do
  { head, tail } <- uncons st.history
  if Array.length st.history > 1 then
    pure $ st { mode = head, history = tail, future = st.mode : st.future }
  else
    pure $ st { mode = head }

redo :: State -> Maybe State
redo st = do
  { head, tail } <- uncons st.future
  pure $ st { mode = head, history = st.mode : st.history, future = tail }

cut :: State -> Maybe State
cut st = do
  traceM "cut"
  clip <- modeToClipboard st.mode
  st <- delete st
  pure $ st { clipboard = clip }

copy :: State -> Maybe State
copy st = do
  traceM "copy"
  clip <- modeToClipboard st.mode
  pure $ st { clipboard = freshenClipboard clip }

freshenClipboard :: Clipboard -> Clipboard
freshenClipboard = case _ of
        EmptyClip -> EmptyClip
        TermClip ctxs ty tm -> TermClip ctxs ty (freshenTerm tm) -- It should be fine to not freshen the type? There are no binders in the type itself, and any type variables bound in the term can't possible show up in the type.
        TermPathClip ctxs1 ty1 tmPath ctxs2 ty2 ->
            let ksub /\ sub /\ tmPath' = freshenTermPath tmPath in
            let sub2 = convertSub ksub in
            let ctxs2' = subAllCtx sub2 ctxs2 in
            let ty2' = applySubType sub2 ty2 in
            TermPathClip ctxs1 ty1 tmPath' ctxs2' ty2'
        _ -> hole' "TODO: do other clipboards for freshenClipboard"

-- TODO: should only freshen if its copy and not cut
modeToClipboard :: Mode -> Maybe Clipboard
modeToClipboard = case _ of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TermCursor ctxs ty _tmPath tm -> pure $ TermClip ctxs ty tm
    _ -> hole' "modeToClipboard"
  SelectMode selectMode -> case selectMode.select of
    TermSelect _tmPath1 ctxs1 ty1 _tm1 tmPath2 ctxs2 ty2 _tm2 _ori -> Just $ TermPathClip ctxs1 ty1 tmPath2 ctxs2 ty2
    _ -> hole' "modeToClipboard"

-- TODO: properly use contexts and freshen variables
paste :: State -> Maybe State
paste st = do
  traceM "paste: TODO: need to implement freshening the clipboard after each paste"
  checkpoint -- TODO: Henry: how can I call freshenClipboard after each successful paste? Well I guess its fine if we freshen after unsuccessful pastes too.
    <$> case st.clipboard of
        EmptyClip -> Nothing
        TermClip ctxs' ty' tm' -> case st.mode of
          CursorMode cursorMode -> case cursorMode.cursorLocation of
--            TermCursor ctxs ty tmPath _tm -> pure $ st { mode = makeCursorMode $ TermCursor ctxs ty (TypeBoundary1 defaultTypeBoundaryMD (Replace ty' ty) List.: tmPath) tm' }
            InsideHoleCursor ctxs ty insideHolePath ->
                let kctxDiff = getKindChangeCtx ctxs'.kctx ctxs.kctx ctxs'.actx ctxs.actx in
                let ctxDiff = getChangeCtx ctxs'.ctx ctxs.ctx in
                let _ /\ chIn = chType kctxDiff ty' in -- ??????
                let ch /\ tm'Diff = chTerm kctxDiff ctxDiff chIn tm' in
                let ty'Diff = snd (getEndpoints ch) in
                -- TODO: finish this implementation! should chIn be used like this? And how should ty'Diff and tm'Diff be used below?
                case runUnify (normThenUnify ctxs.actx ty'Diff ty) of
                    Left msg -> Nothing
                    Right (newTy /\ sub) ->
                        recInsideHolePath {
                            hole1 : \termPath ->
                                pure $ st {mode = makeCursorMode $ TermCursor (subAllCtx sub ctxs) newTy (subTermPath sub termPath.termPath) (subTerm sub tm'Diff)}
                        } {ctxs, ty, insideHolePath}
            _ -> Nothing
          SelectMode _selectMode -> Nothing
        TermPathClip ctxs1' _ty1' tmPath' ctxs2' ty2' -> case st.mode of
          CursorMode cursorMode -> case cursorMode.cursorLocation of
            TermCursor ctxs ty tmPath tm ->
              -- STEP 1: we need to generalize the inside and outside types of tmPath'
              let originalCh = termPathToChange ty2' tmPath' in
              let genCh = generalizeChange originalCh in
              let innerGenTy = fst (getEndpoints genCh) in -- the inner generalized type is what must unify with the type of the term that the cursor is on
              case runUnify (normThenUnify ctxs.actx innerGenTy ty) of
                  Left msg -> Nothing
                  Right (newTy /\ sub) -> -- TODO: this sub needs to be applied to ty, tmPath, and tm. It doesn't need to be applied to tmPath', because that gets changed by a call to chTermPath
                      -- STEP 2: given a specific instantiation of the inner type that will fit at the term, we need to change tmPath' so that it has this type inside
                      let ctxs' /\ tmPath'Changed = chTermPath (Replace (fst (getEndpoints originalCh)) newTy) {ctxs: ctxs2', ty: ty2', term: Hole defaultHoleMD, termPath: tmPath'} in
                      -- STEP 3: get the ctx changes describing what variables have been removed or changed, and apply them to tmPath'Changed
                      let kctxDiff1 = getKindChangeCtx ctxs1'.kctx ctxs.kctx ctxs1'.actx ctxs.actx in -- first get the diff to the top context
                      let ctxDiff1 = getChangeCtx ctxs1'.ctx ctxs.ctx in
                      let kctxDiff2 = threeCaseUnion (\tvc -> unsafeThrow "shouldn't happen paste1") -- then, the diff for the inside adds in everything that was in the bottom context but not the top
                           (\(k /\ tyDef) -> TVarKindChange (kindInject k) (tacInject <$> tyDef)) (\tvc _ -> tvc) kctxDiff1
                           (threeCaseUnion (\k -> (k /\ Nothing)) (\_ -> unsafeThrow "shouldn't happen paste2") (\k tyDef -> k /\ Just tyDef) ctxs2'.kctx ctxs2'.actx) in
                      let ctxDiff2 = threeCaseUnion (\_ -> unsafeThrow "shouldn't happen paste3")
                           (\pty -> VarTypeChange (pTyInject pty)) (\vc _ -> vc) ctxDiff1 ctxs2'.ctx in
--                      let ctxs''' /\ tmPath'Changed' = chTermPath (tyInject ?h)
                      -- TODO: big problem: we need to change the context of the term path here. But we have no way of doing this!!!!!
                      -- One possible janky solution is to make chTermPath accept a context change at the TOP which would allieviate the need for getting *ctxDiff2 anyway, and not require much new code.
                      -- STEP 4: we need to get the typechange going up and ctx change going down and apply them to the term and path in the cursor
                      let ctxCh /\ kctxCh /\ _ /\ _ = downPathToCtxChange ctxs (List.reverse tmPath'Changed) in
                      let tm' = chTermBoundary kctxCh ctxCh (tyInject newTy) tm in
                      let finalCh = termPathToChange newTy tmPath'Changed in
                      let ctxs'' /\ termPathChanged = chTermPath finalCh {ctxs: ctxs, ty: ty, term: tm', termPath: tmPath} in
                      -- TODO TODO TODO TODO: what on earth do I do with the context changes resulting from the two calls to chTermPath???
                      --- Also, I still need to apply the context change from the path downwards!
                      pure $ st { mode = makeCursorMode $ TermCursor ctxs ty (termPathChanged <> tmPath'Changed ) tm}
            _ -> Nothing
          SelectMode selectMode -> case selectMode.select of
--            TermSelect tmPath1 ctxs1 ty1 _tm1 tmPath2 _ctxs2 ty2 tm2 _ori ->
--              pure
--                $ st
--                    { mode =
--                      makeCursorMode
--                        $ TermCursor ctxs1 ty1
--                            ( (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty2 ty2'))
--                                <> tmPath2
--                                <> (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty1' ty1))
--                                <> tmPath1
--                            )
--                            tm2
--                    }
            _ -> Nothing
        _ -> hole' "TODO: do other syntactic cases for paste"

delete :: State -> Maybe State
delete st = do
  traceM "delete"
  checkpoint
    <$> case st.mode of
        CursorMode cursorMode -> case cursorMode.cursorLocation of
          TermCursor ctxs ty path _tm -> do
            let
              cursorLocation' = TermCursor ctxs ty path (freshHole unit)
            pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
          TypeCursor ctxs path ty -> do
            let
              ty' = (freshTHole unit)
              (kctx' /\ ctx') /\ path' = (chTypePath (Replace ty ty') { ctxs, ty, typePath: path })
              ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
              cursorLocation' = TypeCursor ctxs' path' ty'
            pure $ st { mode = CursorMode cursorMode { cursorLocation = cursorLocation' } }
          _ -> hole' "delete: other syntactical kids of cursors"
        SelectMode selectMode -> case selectMode.select of
          TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 _ctxs2 ty2 tm2 _ori ->
            let
              change = termPathToChange ty2 tmPath2
              (kctx' /\ ctx') /\ tmPath1' = chTermPath (invert change) { term: tm1, ty: ty1, ctxs: ctxs1, termPath: tmPath1 }
              (ctx /\ kctx /\ _mdctx /\ _mdkctx) = downPathToCtxChange ctxs1 (List.reverse tmPath2)
              tm2' = chTermBoundary (invertKCtx kctx) (invertCtx ctx) (tyInject ty2) tm2
              ctxs' = ctxs1 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
            in
              pure $ st { mode = makeCursorMode $ TermCursor ctxs' ty2 tmPath1' tm2' }
          TypeSelect topPath _ctxs1 _ty1 middlePath ctxs2 ty2 _ori ->
            let
              change = typePathToChange ty2 middlePath
            in
              --chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> CAllContext /\ UpPath
              let
                (kctx' /\ ctx') /\ topPath' = chTypePath (invert change) { ty: ty2, ctxs: ctxs2, typePath: topPath }
              in
                let
                  ctxs' = ctxs2 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
                in
                  pure $ st { mode = makeCursorMode $ TypeCursor ctxs' topPath' ty2 }
          TypeBindListSelect topPath _ctxs1 _tyBinds1 middlePath ctxs2 tyBinds2 _ori ->
            let
              innerCh = chTypeBindList tyBinds2
            in
              let
                change = typeBindPathToChange innerCh middlePath
              in
                let
                  topPath' = chListTypeBindPath (invertListTypeBindChange change) { ctxs: ctxs2, tyBinds: tyBinds2, listTypeBindPath: topPath }
                in
                  pure $ st { mode = makeCursorMode $ TypeBindListCursor ctxs2 topPath' tyBinds2 }
          _ -> hole' "delete: other syntactical kinds of selects"

escape :: State -> Maybe State
escape st = case st.mode of
  CursorMode cursorMode -> do
    pure $ st { mode = CursorMode cursorMode { query = emptyQuery } }
  SelectMode selectMode -> do
    pure $ st { mode = makeCursorMode (selectToCursorLocation selectMode.select) }
