module TypeCraft.Purescript.ModifyState where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.TypeChangeAlgebra2
import TypeCraft.Purescript.Util

import Data.Argonaut (Json, JsonDecodeError, decodeJson, encodeJson, parseJson)
import Data.Argonaut.Encode (toJsonString)
import Data.Array ((:), uncons)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.List (length)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Maybe (maybe)
import Data.Tuple (snd, fst)
import Data.Tuple.Nested (type (/\), (/\))
import Debug (trace, traceM)
import Debug as Debug
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Alpha (applySubType, subAllCtx, subTermPath, subInsideHolePath, subTerm, applySubChange)
import TypeCraft.Purescript.Alpha (convertSub)
import TypeCraft.Purescript.Alpha (subTypePath)
import TypeCraft.Purescript.ChangePath (chListCtrParamPath, chListCtrPath, chListTypeBindPath, chTermPath, chTypePath)
import TypeCraft.Purescript.CursorMovement (cursorLocationToSelect, getCursorChildren, goTop, goUp_n, moveSelectLeft, moveSelectRight, stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.CursorMovementHoles (stepCursorNextHolelike, stepCursorPrevHolelike)
import TypeCraft.Purescript.Dentist (downPathToCtxChange, termPathToChange, typeBindPathToChange, typePathToChange)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.ModifyIndentation (toggleIndentation)
import TypeCraft.Purescript.PathRec (recInsideHolePath)
import TypeCraft.Purescript.Prelude (preludeContexts)
import TypeCraft.Purescript.SmallStep.Freshen (freshenTerm, freshenTermPath)
import TypeCraft.Purescript.State (Clipboard(..), Completion(..), CursorLocation(..), CursorMode, Mode(..), Program(..), Query, Select(..), State, botSelectOrientation, emptyQuery, getCompletion, makeCursorMode, selectToCursorLocation, topSelectOrientation)
import TypeCraft.Purescript.Unification (runUnify, normThenUnify)

handleKey :: Key -> State -> Maybe State
handleKey key st
  | key.key == "p" && (key.metaKey || key.ctrlKey) = do
    -- Debug.traceM "==[ current state.mode ]====================================="
    -- Debug.traceM $ show st
    -- Debug.traceM "============================================================="
    case st.mode of
      CursorMode { cursorLocation: TermCursor _ctxs ty path tm } -> do
        Debug.traceM "==[ path ]====================================="
        Debug.traceM $ show path
        Debug.traceM "==[ term ]====================================="
        Debug.traceM $ show tm
        Debug.traceM "==[ type ]====================================="
        Debug.traceM $ show ty
      _ -> Nothing
    Just st

-- !TODO move all the stuff that isnt specific to a specific kind of cursor to
-- happen just at CursorMode rather htan in each kind of cursor (or, can keep
-- separate and then have to manage specifically?)
handleKey key st = case st.mode of
  CursorMode cursorMode -> case cursorMode.cursorLocation of
    TypeBindCursor ctxs path (TypeBind md tyVarId)
      | key.key == " " -> moveCursorNextHolelike st
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TypeBindCursor ctxs path (TypeBind md { varName = varName } tyVarId) } }
    TermBindCursor ctxs path (TermBind md tmVarId)
      | key.key == " " -> moveCursorNextHolelike st
      | Just varName <- manipulateString key md.varName -> pure $ st { mode = CursorMode cursorMode { cursorLocation = TermBindCursor ctxs path (TermBind md { varName = varName } tmVarId) } }
    --    CtrParamListCursor ctxs path ctrs -> hole' "handleKey CtrParamListCursor" -- Jacob Note: why was this line here? I'm not sure.
    _
      | key.key == " " ->
        case submitQuery st of
            Just st' -> Just st'
            Nothing -> moveCursorNextHolelike st
      | Just query <- manipulateQuery key st cursorMode -> do
        -- note that we don't `checkpoint` here, since every little modification
        -- of the query string and selection shouldn't by undoable
        pure $ st { mode = CursorMode cursorMode { query = query } }
      -- undo/redo
      | (key.ctrlKey || key.metaKey) && key.key == "z" && key.shiftKey -> redo st
      | (key.ctrlKey || key.metaKey) && key.key == "z" -> undo st
      -- jump to next/prev holelike
      | key.altKey && key.key == "ArrowLeft" -> moveCursorPrevHolelike st
      | key.altKey && key.key == "ArrowRight" -> moveCursorNextHolelike st
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

-- | The situations where checkpoints are made are:
-- | - before a query submit
-- | - before a paste
-- | - before a delete
-- |   - note that cut = copy then delete
checkpoint :: State -> State
checkpoint st = st { history = st.mode : st.history }

submitQuery :: State -> Maybe State
submitQuery st0 = case st0.mode of
  CursorMode cursorMode -> do
    let
      st = checkpoint st0 { mode = CursorMode cursorMode { query { string = "" } } }
    compl <- 
      case Int.fromString cursorMode.query.string of
        -- !TODO implement integer literals
        Just _i -> Nothing -- Just $ CompletionTerm ?a ?a
        Nothing -> getCompletion cursorMode.query
    cursorMode' <- submitCompletion cursorMode compl
    -- checkpoints the pre-submission mode with a cleared query string
    pure $ st { mode = CursorMode cursorMode' }
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
          (Hole1 _) List.: termPath' -> termPath'
          _ -> unsafeThrow "Shouldn't happen"
        loc' = stepCursorNextHolelike (TermCursor ctxs' ty' termPath tm)
      in
        pure
          { cursorLocation: loc'
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

        (kctx' /\ ctx') /\ path'' = chTermPath ch { ctxs: ctxs', ty: ty', termPath: path', term: tm } Nothing

        tm'' = chTermBoundary kctx' ctx' (tyInject ty') tm'

        ctxs'' = ctxs' { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }

        chCtxs = downPathToCtxChange ctxs'' (List.reverse pathNew')

        newCtxs = snd (getAllEndpoints chCtxs)

        -- make new cursor
        loc = TermCursor newCtxs ty' (pathNew' <> path'') tm''
        -- move to top of cursor 
        loc' = goUp_n (length pathNew') loc
        -- move to next hole
        loc'' = stepCursorNextHolelike loc'
      in
        pure
          { cursorLocation: loc''
          , query: emptyQuery
          }
    -- CompletionTermPath2 _ newState ->
    --   pure
    --     { cursorLocation: newState unit
    --     , query: emptyQuery
    --     }
    _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty -> case compl of
    CompletionType ty' sub ->
      -- TODO: This should really be in the InsideTypeHoleCursor case!!!!!!!!!!!!!!!
      let path' = subTypePath sub path in
      let ctxs' = subAllCtx sub ctxs in
          --      let (kctx' /\ ctx') /\ path' = chTypePath (Replace ty ty') { ctxs, ty, typePath: path } in
          --      let ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') } in
      pure
        { cursorLocation: stepCursorNextHolelike (TypeCursor ctxs' path' ty')
        , query: emptyQuery
        }
    CompletionTypePath pathNew ch ->
      let
        (kctx' /\ ctx') /\ path' = chTypePath ch { ctxs, ty: ty, typePath: path }
        ctxs' = ctxs { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }

        -- make new cursor
        loc = TypeCursor ctxs' (pathNew <> path') ty
        -- move to top of cursor 
        loc' = goUp_n (length pathNew) loc
        -- move to next hole
        loc'' = stepCursorNextHolelike loc'
      in
          pure
            { cursorLocation: loc''
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

moveCursorPrev :: State -> Maybe State
moveCursorPrev st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorBackwards cursorLocation) }
  _ -> do moveCursorPrev =<< escape st

moveCursorNext :: State -> Maybe State
moveCursorNext st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorForwards cursorLocation) }
  _ -> moveCursorNext =<< escape st

moveCursorNextHolelike :: State -> Maybe State
moveCursorNextHolelike st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorNextHolelike cursorLocation) }
  _ -> moveCursorNextHolelike =<< escape st

moveCursorPrevHolelike :: State -> Maybe State
moveCursorPrevHolelike st = case st.mode of
  CursorMode { cursorLocation } -> pure $ st { mode = makeCursorMode (stepCursorPrevHolelike cursorLocation) }
  _ -> moveCursorNextHolelike =<< escape st

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
  traceM "ModifyState.undo"
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
    let
      ksub /\ sub /\ tmPath' = freshenTermPath tmPath

      sub2 = convertSub ksub

      termVarIDMap x = case Map.lookup x sub of -- TODO: This stuff should probably be in a different function?
        Just y -> y
        Nothing -> x

      typeVarIDMap x = case Map.lookup x ksub of
        Just y -> y
        Nothing -> x

      ctxs2' =
        subAllCtx sub2
          ctxs2
            { ctx = mapKeys termVarIDMap ctxs2.ctx
            , mdctx = mapKeys termVarIDMap ctxs2.mdctx
            , kctx = mapKeys typeVarIDMap ctxs2.kctx
            , mdkctx = mapKeys typeVarIDMap ctxs2.mdkctx
            }

      ty2' = applySubType sub2 ty2
    in
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

paste :: State -> Maybe State
paste st0 = do
  let
    st = checkpoint st0
  st' <- pasteImpl st
  pure $ st' { clipboard = freshenClipboard st'.clipboard }

-- TODO: properly use contexts and freshen variables
pasteImpl :: State -> Maybe State
pasteImpl st = case st.clipboard of
  EmptyClip -> Nothing
  TermClip ctxs' ty' tm' -> case st.mode of
    CursorMode cursorMode -> case cursorMode.cursorLocation of
      TermCursor ctxs ty tmPath _tm -> pure $ st { mode = makeCursorMode $ TermCursor ctxs ty (TypeBoundary1 defaultTypeBoundaryMD (Replace ty' ty) List.: tmPath) tm' }
      InsideHoleCursor ctxs ty insideHolePath ->
        let
          kctxDiff = getKindChangeCtx ctxs'.kctx ctxs.kctx ctxs'.actx ctxs.actx ctxs'.mdkctx ctxs.mdkctx

          ctxDiff = getChangeCtx ctxs'.ctx ctxs.ctx ctxs'.mdctx ctxs.mdctx

          _ /\ chIn = chType kctxDiff ty'

          ch /\ tm'Diff = chTerm kctxDiff ctxDiff chIn tm'

          ty'Diff = snd (getEndpoints ch)
        -- TODO: finish this implementation! should chIn be used like this? And how should ty'Diff and tm'Diff be used below?
        in
          case runUnify (normThenUnify ctxs.actx ty'Diff ty) of
            Left msg -> Nothing
            Right (newTy /\ sub) ->
              recInsideHolePath
                { hole1:
                    \_md termPath ->
                      pure $ st { mode = makeCursorMode $ TermCursor (subAllCtx sub ctxs) newTy (subTermPath sub termPath.termPath) (subTerm sub tm'Diff) }
                }
                { ctxs, ty, insideHolePath }
      _ -> Nothing
    SelectMode _selectMode -> Nothing
  TermPathClip ctxs1'PreSub _ty1' pastePathPreSub ctxs2'PreSub ty2'PreSub -> case st.mode of
    CursorMode cursorMode -> case cursorMode.cursorLocation of
      TermCursor ctxsPreSub tyPreSub tmPathPreSub tmPreSub -> do
        -- STEP 1: we need to generalize the inside and outside types of tmPath'
        traceM "STEP 1 of termPath paste: generalize the path"
        let originalChPreSub = termPathToChange ty2'PreSub pastePathPreSub
        let genCh = generalizeChange originalChPreSub
        let innerGenTy = fst (getEndpoints genCh)
        -- the inner generalized type is what must unify with the type of the term that the cursor is on
        case runUnify (normThenUnify ctxsPreSub.actx innerGenTy tyPreSub) of
          Left msg -> Nothing
          -- TODO: this sub needs to be applied to ty, tmPath, and tm. It doesn't need to be applied to tmPath', because that gets changed by a call to chTermPath
          Right (newTy /\ sub) -> do
            -- some of the holes getting subbed essentially don't exist, and were only created by generalizeChange. However, some are real holes in the program, and
                -- Those actually need to get substituted everywhere.
            traceM ("beginning substitutions for termPath paste. sub is: " <> show sub)
            let pastePath = subTermPath sub pastePathPreSub
            let ctxs1' = subAllCtx sub ctxs1'PreSub
            let ctxs2' = subAllCtx sub ctxs2'PreSub
            let ty2' = applySubType sub ty2'PreSub
            let ctxs = subAllCtx sub ctxsPreSub
            let ty = applySubType sub tyPreSub
            let tmPath = subTermPath sub tmPathPreSub
            let tm = subTerm sub tmPreSub
            let originalCh = applySubChange sub originalChPreSub
            -- STEP 2: get the ctx changes describing what variables have been removed or changed, and apply them to tmPath'Changed
            traceM "STEP 2 of termPath paste: get context diff"
            let kctxDiff1 = getKindChangeCtx ctxs1'.kctx ctxs.kctx ctxs1'.actx ctxs.actx ctxs1'.mdkctx ctxs.mdkctx
              -- first get the diff to the top context
            let ctxDiff1 = getChangeCtx ctxs1'.ctx ctxs.ctx ctxs1'.mdctx ctxs.mdctx
            -- STEP 3: given a specific instantiation of the inner type that will fit at the term, we need to change tmPath' so that it has this type inside
            traceM "STEP 3 of termPath paste: adjust path to be pasted"
            -- Also, apply the context changes while were at it:
            let (kctx' /\ ctx') /\ pastePath2 =
                 chTermPath (Replace (fst (getEndpoints originalCh)) newTy) { ctxs: ctxs2', ty: ty2', term: Hole defaultHoleMD, termPath: pastePath }
                  (Just (kctxDiff1 /\ ctxDiff1))
            --                      let ctxs''' /\ tmPath'Changed' = chTermPath (tyInject ?h)
            -- STEP 4: we need to get the typechange going up and ctx change going down and apply them to the term and path in the cursor
            traceM "STEP 4 of termPath paste: get changes and apply to program"
            traceM ("reverse pastePath2 is: " <> show (List.reverse pastePath2))
            let (ctxCh /\ kctxCh /\ mdctxCh /\ mdkctxCh) = downPathToCtxChange ctxs (List.reverse pastePath2)
            traceM ("ctxCh is: " <> show ctxCh)
            let finalCh = termPathToChange newTy pastePath2
              --                      trace ("finalCh is: " <> show finalCh) \_ ->
              -- These changes are at the top of the path to be pasted
            let (kctxCh2 /\ ctxCh2) /\ termPathChanged = chTermPath finalCh { ctxs: ctxs, ty: ty, term: Hole defaultHoleMD, termPath: tmPath } Nothing
            --                      let tm' = chTermBoundary kctxCh ctxCh (tyInject newTy) tm in
            --                      trace ("ctxCh2 is: " <> show ctxCh2) \_ ->
            traceM "STEP 4.5"
            let (kctxCh2bottom /\ ctxCh2bottom) /\ pastePath3 = chTermPath (tyInject newTy){ ctxs: ctxs2'{ctx= snd (getCtxEndpoints ctx'),
                kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx')} {-technically this doesn't update mdctx and mdkctx, but I think its fine?-},
                ty: newTy, term: Hole defaultHoleMD, termPath: pastePath2 } (Just (kctxCh2 /\ ctxCh2))
            traceM ("ctxCh2bottom is: " <> show ctxCh2bottom)
            let fullKCtxCh = (composeKCtx kctxCh kctxCh2bottom)
            let fullCtxCh = (composeCtxs ctxCh ctxCh2bottom)
            let tm' = chTermBoundary fullKCtxCh fullCtxCh (tyInject newTy) tm
              --                      if not (kCtxIsId kctxShouldBeId) || not (ctxIsId ctxShouldBeId) then unsafeThrow "shouldn't happen in termPath paste" else
              --- Also, I still need to apply the context change from the path downwards!
            let ctxs' = snd (getAllEndpoints (fullCtxCh /\ fullKCtxCh /\ mdctxCh /\ mdkctxCh))
            traceM ("ctxs'.ctx is: " <> show ctxs'.ctx)
            traceM ("Made it to the end of termpath paste stuff")
            pure $ st { mode = makeCursorMode $ TermCursor ctxs' ty (pastePath3 <> termPathChanged) tm' }
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
delete st0 =
  let
    st = checkpoint st0
  in
    case st.mode of
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
        TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 _ctxs2 ty2 tm2 _ori -> do
          let
            change = termPathToChange ty2 tmPath2
            (kctx' /\ ctx') /\ tmPath1' = chTermPath (invert change) { term: tm1, ty: ty1, ctxs: ctxs1, termPath: tmPath1 } Nothing
            (ctx /\ kctx /\ _mdctx /\ _mdkctx) = downPathToCtxChange ctxs1 (List.reverse tmPath2)
            -- TODO: should these compositions go the other way around?
            tm2' = chTermBoundary (composeKCtx (invertKCtx kctx) kctx') (composeCtxs (invertCtx ctx) ctx') (tyInject ty2) tm2

            ctxs' = ctxs1 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
          pure $ st { mode = makeCursorMode $ TermCursor ctxs' ty2 tmPath1' tm2' }
        TypeSelect topPath _ctxs1 _ty1 middlePath ctxs2 ty2 _ori -> do
          let
            change = typePathToChange ty2 middlePath

            (kctx' /\ ctx') /\ topPath' = chTypePath (invert change) { ty: ty2, ctxs: ctxs2, typePath: topPath }

            ctxs' = ctxs2 { ctx = snd (getCtxEndpoints ctx'), kctx = snd (getKCtxTyEndpoints kctx'), actx = snd (getKCtxAliasEndpoints kctx') }
          pure $ st { mode = makeCursorMode $ TypeCursor ctxs' topPath' ty2 }
        TypeBindListSelect topPath _ctxs1 _tyBinds1 middlePath ctxs2 tyBinds2 _ori -> do
          let
            innerCh = chTypeBindList tyBinds2

            change = typeBindPathToChange innerCh middlePath

            topPath' = chListTypeBindPath (invertListTypeBindChange change) { ctxs: ctxs2, tyBinds: tyBinds2, listTypeBindPath: topPath }
          pure $ st { mode = makeCursorMode $ TypeBindListCursor ctxs2 topPath' tyBinds2 }
        _ -> hole' "delete: other syntactical kinds of selects"

escape :: State -> Maybe State
escape st = case st.mode of
  CursorMode cursorMode -> do
    pure $ st { mode = CursorMode cursorMode { query = emptyQuery } }
  SelectMode selectMode -> do
    pure $ st { mode = makeCursorMode (selectToCursorLocation selectMode.select) }

setProgram :: Program -> State -> Maybe State
setProgram prog st = do
  let loc = TermCursor preludeContexts prog.type_ mempty prog.term
  pure st { name = prog.name, mode = CursorMode { cursorLocation: loc, query: emptyQuery } }

getProgram :: State -> Maybe Program
getProgram st = case st.mode of 
  CursorMode cursorMode -> do
    case goTop cursorMode.cursorLocation of
      TermCursor _ctxs ty up tm | List.length up == 0 -> do
        pure {name: st.name, type_: ty, term: tm}
      _ -> unsafeThrow "saveProgram: after going to top of program, shouldn't still have steps in the path"
  SelectMode _ -> getProgram =<< escape st

setProgramJsonString :: String -> State -> Maybe State 
setProgramJsonString str st = do
  let 
    ei_prog :: Either JsonDecodeError Program
    ei_prog = do
      json <- parseJson str
      decodeJson json
  case ei_prog of
    Left err -> unsafeThrow $ "loadProgramJsonString: decoding json error: " <> show err 
    Right prog -> setProgram prog st

getProgramJsonString :: State -> Maybe String
getProgramJsonString st = do
  prog <- getProgram st 
  pure $ toJsonString $ encodeJson prog

setName :: String -> State -> State 
setName str st = st { name = str }

getName :: State -> String 
getName st = st.name
