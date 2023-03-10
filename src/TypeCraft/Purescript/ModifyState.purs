module TypeCraft.Purescript.ModifyState where

import Data.Tuple.Nested ((/\))
import Prelude
import TypeCraft.Purescript.Alpha (applySubType, subAllCtx, subTermPath)
import TypeCraft.Purescript.ChangePath (chListCtrParamPath, chListCtrPath, chListTypeBindPath, chTermPath, chTypePath)
import TypeCraft.Purescript.ChangeTerm (chTermBoundary, chTypeBindList)
import TypeCraft.Purescript.CursorMovement (cursorLocationToSelect, getCursorChildren, moveSelectLeft, moveSelectRight, stepCursorBackwards, stepCursorForwards)
import TypeCraft.Purescript.Dentist (downPathToCtxChange, termPathToChange, typeBindPathToChange, typePathToChange)
import TypeCraft.Purescript.Grammar (Change(..), TermBind(..), Tooth(..), TypeBind(..), freshHole, freshTHole, tyInject)
import TypeCraft.Purescript.State (Clipboard(..), Completion(..), CursorLocation(..), CursorMode, Mode(..), Query, Select(..), State, botSelectOrientation, emptyQuery, getCompletion, makeCursorMode, selectToCursorLocation, topSelectOrientation)
import TypeCraft.Purescript.TypeChangeAlgebra (getAllEndpoints, getCtxEndpoints, getKCtxAliasEndpoints, getKCtxTyEndpoints, invert, invertListTypeBindChange)
import Data.Array ((:), uncons)
import Data.Array as Array
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Debug (traceM)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.MD (defaultTypeBoundaryMD)
import TypeCraft.Purescript.ManipulateQuery (manipulateQuery)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.ModifyIndentation (toggleIndentation)
import TypeCraft.Purescript.Util (hole')

handleKey :: Key -> State -> Maybe State
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
    cursorMode' <- submitQuery' cursorMode
    -- checkpoints the pre-submission mode with a cleared query string
    pure
      $ (checkpoint st { mode = CursorMode cursorMode { query { string = "" } } })
          { mode = CursorMode cursorMode' }
  _ -> Nothing

modifyQuery :: (Query -> Query) -> State -> Maybe State
modifyQuery f st = case st.mode of
  CursorMode cursorMode -> pure st { mode = CursorMode cursorMode { query = f cursorMode.query } }
  _ -> Nothing

submitQuery' :: CursorMode -> Maybe CursorMode
submitQuery' cursorMode = case cursorMode.cursorLocation of
  InsideHoleCursor ctxs ty path ->
    getCompletion cursorMode.query
      >>= case _ of
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
          _ -> Nothing
  TermCursor ctxs ty path tm ->
    getCompletion cursorMode.query
      >>= case _ of
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
              -- TODO: is this all done in the proper order?
              path' = subTermPath sub path

              pathNew' = subTermPath sub pathNew

              ty' = applySubType sub ty

              ctxs' = subAllCtx sub ctxs

              (kctx' /\ ctx') /\ path'' = chTermPath ch { ctxs: ctxs', ty: ty', termPath: path', term: tm }

              tm' = chTermBoundary kctx' ctx' (tyInject ty') tm

              ctxs'' =
                ctxs'
                  { ctx = snd (getCtxEndpoints ctx')
                  , kctx = snd (getKCtxTyEndpoints kctx')
                  , actx = snd (getKCtxAliasEndpoints kctx')
                  }

              chCtxs = downPathToCtxChange ctxs'' (List.reverse pathNew')

              newCtxs = snd (getAllEndpoints chCtxs)
            in
              pure
                { cursorLocation: TermCursor newCtxs ty' (pathNew' <> path'') tm'
                , query: emptyQuery
                }
          CompletionTermPath2 _ newState ->
            pure
              { cursorLocation: newState unit
              , query: emptyQuery
              }
          _ -> unsafeThrow "tried to submit a non-CompletionTerm* completion at a TermCursor"
  TypeCursor ctxs path ty ->
    getCompletion cursorMode.query
      >>= case _ of
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
  CtrListCursor ctxs path ctrs ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionCtrListPath pathNew ch ->
            let
              path' = chListCtrPath ch { ctxs, listCtrPath: path, ctrs }
            in
              pure
                { cursorLocation: CtrListCursor ctxs (pathNew <> path') ctrs
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  CtrParamListCursor ctxs path ctrParams ->
    getCompletion cursorMode.query
      >>= case _ of
          CompletionCtrParamListPath pathNew ch ->
            let
              path' = chListCtrParamPath ch { ctxs, ctrParams, listCtrParamPath: path }
            in
              pure
                { cursorLocation: CtrParamListCursor ctxs (pathNew <> path') ctrParams
                , query: emptyQuery
                }
          _ -> unsafeThrow "tried to submit a non-CompletionCursorList at a CtrListCursor"
  TypeBindListCursor ctxs path tyBinds ->
    getCompletion cursorMode.query
      >>= case _ of
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
  pure $ st { clipboard = clip }

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
  traceM "paste"
  checkpoint
    <$> case st.clipboard of
        EmptyClip -> Nothing
        TermClip _ctxs' ty' tm' -> case st.mode of
          CursorMode cursorMode -> case cursorMode.cursorLocation of
            TermCursor ctxs ty tmPath _tm -> pure $ st { mode = makeCursorMode $ TermCursor ctxs ty (TypeBoundary1 defaultTypeBoundaryMD (Replace ty' ty) List.: tmPath) tm' }
            _ -> Nothing
          SelectMode _selectMode -> Nothing
        TermPathClip _ctxs1' ty1' tmPath' _ctxs2' ty2' -> case st.mode of
          CursorMode cursorMode -> case cursorMode.cursorLocation of
            TermCursor ctxs ty tmPath tm ->
              pure
                $ st
                    { mode =
                      makeCursorMode
                        $ TermCursor ctxs ty
                            ( (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty ty2'))
                                <> tmPath'
                                <> (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty1' ty))
                                <> tmPath
                            )
                            tm
                    }
            _ -> Nothing
          SelectMode selectMode -> case selectMode.select of
            TermSelect tmPath1 ctxs1 ty1 _tm1 tmPath2 _ctxs2 ty2 tm2 _ori ->
              pure
                $ st
                    { mode =
                      makeCursorMode
                        $ TermCursor ctxs1 ty1
                            ( (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty2 ty2'))
                                <> tmPath2
                                <> (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (Replace ty1' ty1))
                                <> tmPath1
                            )
                            tm2
                    }
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
            in
              let
                (kctx' /\ ctx') /\ tmPath1' = chTermPath (invert change) { term: tm1, ty: ty1, ctxs: ctxs1, termPath: tmPath1 }
              in
                let
                  (ctx /\ kctx /\ _mdctx /\ _mdkctx) = downPathToCtxChange ctxs1 (List.reverse tmPath2)
                in
                  let
                    tm2' = chTermBoundary kctx ctx (tyInject ty2) tm2
                  in
                    let
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
