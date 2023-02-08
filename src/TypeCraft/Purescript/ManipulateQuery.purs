module TypeCraft.Purescript.ManipulateQuery where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Unification
import Control.Monad.Writer as Writer
import Data.Array (any)
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.String as String
import Data.String.Regex as Regex
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID (UUID)
import Debug (trace)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.CursorMovement (stepCursor_n)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Query, State, makeCursorMode)
import TypeCraft.Purescript.Util (hole, hole')
import TypeCraft.Purescript.Util (lookup')

isNonemptyQueryString :: Query -> Boolean
isNonemptyQueryString query = not $ String.null query.string

manipulateQuery :: Key -> State -> CursorMode -> Maybe Query
manipulateQuery key st cursorMode@{ query: query@{ string, completionGroup_i, completionGroupItem_i } }
  | key.key == "ArrowUp" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i - 1 }
  | key.key == "ArrowDown" && isNonemptyQueryString query = pure query { completionGroup_i = completionGroup_i + 1 }
  | key.key == "ArrowLeft" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i - 1 }
  | key.key == "ArrowRight" && isNonemptyQueryString query = pure query { completionGroupItem_i = query.completionGroupItem_i + 1 }
  | otherwise = do
    string' <- manipulateString key string
    pure
      query
        { string = string'
        , completionGroup_i = 0
        , completionGroupItem_i = 0
        , completionGroups = calculateCompletionsGroups string' st cursorMode
        }

kindaStartsWith :: String -> String -> Boolean
kindaStartsWith str pat =
  and
    [ len_str > 0 -- string can't be empty
    , len_pat > 0 -- patfix can't be empty
    , len_pat >= len_str
    , isJust $ String.stripPrefix (String.Pattern str) pat
    ]
  where
  len_str = String.length str

  len_pat = String.length pat

kindaStartsWithAny :: String -> Array String -> Boolean
kindaStartsWithAny str pats = String.length str > 0 && any (str `kindaStartsWith` _) pats

isValidTypeBindLabel_Regex :: Regex.Regex
isValidTypeBindLabel_Regex = case Regex.regex "^[a-zA-Z0-9]*$" mempty of
  Left msg -> unsafeThrow $ "isValidTypeBindLabel_Regex: " <> msg
  Right reg -> reg

isValidTypeBindLabel :: String -> Boolean
isValidTypeBindLabel = Regex.test isValidTypeBindLabel_Regex

calculateCompletionsGroups :: String -> State -> CursorMode -> Array (Array Completion)
calculateCompletionsGroups str st cursorMode = case cursorMode.cursorLocation of
  TermCursor ctxs ty path tm ->
    Writer.execWriter do
      -- Var
      traverse_
        ( \(id /\ varName) -> case Map.lookup id ctxs.ctx of
            Nothing -> unsafeThrow $ "the entry '" <> show (id /\ varName) <> "' was found in the ctxs.mdctx, but not in the ctxs.ctx: '" <> show ctxs.ctx <> "'"
            Just pty ->
              when (str `kindaStartsWith` varName) do
                case runUnify (fillNeutral ctxs.actx pty id ty) of
                  Left _msg -> pure unit
                  Right (tm' /\ sub) -> Writer.tell [ [ CompletionTerm tm' sub { subTypeVars = Map.empty } ] ] -- TODO: Jacob: why would there be subTypeVars here anyway? I'm confused about that. Isn't unification for holes?
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- Lambda
      when (str `kindaStartsWithAny` [ "lam", "\\" ])
        $ Writer.tell
            [ [ let
                  alpha = freshTHole unit

                  tmBind = freshTermBind Nothing
                in
                  CompletionTermPath -- lam (~ : alpha) ↦ ({} : ty)
                    (List.singleton $ Lambda3 defaultLambdaMD tmBind alpha ty)
                    (Plus alpha (tyInject ty))
                    (stepCursor_n (-2)) -- step to bind
              ]
            ]
      -- Let
      when (str `kindaStartsWith` "let")
        $ Writer.tell
            [ [ CompletionTermPath -- let ~<∅> : alpha = ? in {} : ty
                  (List.singleton $ Let5 defaultLetMD (freshTermBind Nothing) List.Nil (freshHole unit) (freshTHole unit) ty)
                  (tyInject ty)
                  (stepCursor_n (-4)) -- step to bind
              ]
            ]
      -- App
      when (str `kindaStartsWithAny` [ " ", "$" ])
        $ case ty of -- TODO: should really be if the type UNIFIES with an Arrow, instead of IS an arrow...
            Arrow _ ty1 ty2 ->
              Writer.tell
                [ [ CompletionTermPath -- ({} ?)
                      (List.singleton $ App1 defaultAppMD (freshHole unit) ty1 ty2)
                      (Minus ty1 (tyInject ty2))
                      (stepCursor_n 1) -- step to arg
                  ]
                ]
            _ -> pure unit
      -- TLet
      when (str `kindaStartsWith` "tlet")
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ TLet4 defaultTLetMD (freshTypeBind Nothing) List.Nil (freshTHole unit) ty)
                  (tyInject ty)
                  (stepCursor_n (-3)) -- step to bind
              ]
            ]
      -- Data
      when (str `kindaStartsWith` "data")
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ Data4 defaultGADTMD (freshTypeBind Nothing) List.Nil List.Nil ty)
                  (tyInject ty)
                  (stepCursor_n (-3)) -- step to bind
              ]
            ]
      -- TypeBoundary
      when (str `kindaStartsWithAny` [ "{" ])
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (tyInject ty))
                  (tyInject ty)
                  identity
              ]
            ]
      -- -- Hole
      -- when (str `kindaStartsWithAny` [ "hole", "?" ])
      --   $ Writer.tell
      --       [ [ CompletionTerm
      --             (freshHole unit) -- ty
      --             { subTypeVars: Map.empty, subTHoles: Map.empty }
      --         ]
      --       ]
      -- Buffer
      when (str `kindaStartsWithAny` [ "buf", "#" ])
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ Buffer3 defaultBufferMD (freshHole unit) (freshTHole unit) ty)
                  (tyInject ty)
                  (stepCursor_n (-2)) -- step to buffer term
              ]
            ]
  TypeCursor ctxs path ty ->
    trace ("Debug while looking for type completions: " <> show (Map.values ctxs.mdkctx)) \_ ->
      Writer.execWriter do
        -- TNeu
        traverse_
          ( \(id /\ tyName) -> case Map.lookup id ctxs.kctx of
              Nothing -> unsafeThrow $ "the entry '" <> show (id /\ tyName) <> "' was found in the ctxs.mdkctx, but not in the ctxs.kctx: '" <> show ctxs.ctx <> "'"
              Just kind -> case ty of
                THole md x ->
                  when (str `kindaStartsWith` tyName) do
                    let
                      cTy = (makeEmptyTNeu id kind)
                    Writer.tell [ [ CompletionType cTy { subTypeVars: Map.empty, subTHoles: Map.insert x cTy Map.empty } ] ]
                _ -> pure unit
          )
          (Map.toUnfoldable ctxs.mdkctx :: Array (UUID /\ String))
        -- Arrow
        when (str `kindaStartsWithAny` [ "->" ])
          $ Writer.tell
              [ [ let
                    thole = freshTHole unit
                  in
                    CompletionTypePath
                      (List.singleton $ Arrow2 defaultArrowMD thole)
                      (Plus thole (tyInject ty))
                ]
              ]
  -- THole -- Jacob note: I don't think it makes sense to query holes. Instead, the delete/backspace button does that.
  --      when (str `kindaStartsWithAny` [ "hole", "?" ])
  --        $ Writer.tell
  --            [ [ CompletionType (freshTHole unit) emptySub
  --              ]
  --            ]
  TypeBindListCursor ctxs path tyBinds ->
    Writer.execWriter do
      -- add a type bind
      when (str `kindaStartsWithAny` [ " ", "," ])
        $ Writer.tell
            [ let
                newTyBind = (freshTypeBind Nothing)
              in
                [ CompletionTypeBindListPath (List.singleton $ TypeBindListCons2 newTyBind) (ListTypeBindChangePlus newTyBind (chTypeBindList tyBinds)) ]
            ]
      when (isValidTypeBindLabel str)
        $ Writer.tell
            [ let
                newTyBind = freshTypeBind (Just str)
              in
                [ CompletionTypeBindListPath (List.singleton $ TypeBindListCons2 newTyBind) (ListTypeBindChangePlus newTyBind (chTypeBindList tyBinds)) ]
            ]
  CtrListCursor ctxs path ctrs ->
    Writer.execWriter do
      -- add a constructor
      when (str `kindaStartsWithAny` [ "|"  ])
        $ Writer.tell
            [ [ let
                  kctx = kCtxInject ctxs.kctx ctxs.actx
                in
                  let
                    ctrCh = fst (chCtrList kctx ctrs)
                  in
                    let
                      newCtr = (Constructor defaultCtrMD (freshTermBind Nothing) List.Nil)
                    in
                      CompletionCtrListPath (List.singleton $ CtrListCons2 newCtr)
                        (ListCtrChangePlus newCtr ctrCh)
              ]
            ]
  CtrParamListCursor ctxs path ctrParams ->
    Writer.execWriter do
      -- add a constructor param
      when (str `kindaStartsWithAny` [ " ", "," ])
        $ Writer.tell
            [ [ let
                  kctx = kCtxInject ctxs.kctx ctxs.actx
                in
                  let
                    ctrParamCh = fst (chParamList kctx ctrParams)
                  in
                    let
                      newCtrParam = (CtrParam defaultCtrParamMD (freshTHole unit))
                    in
                      CompletionCtrParamListPath (List.singleton $ CtrParamListCons2 newCtrParam)
                        (ListCtrParamChangePlus newCtrParam ctrParamCh)
              ]
            ]
  _ -> [] -- TODO: impl

makeEmptyTNeu :: TypeVarID -> Kind -> Type
makeEmptyTNeu x k = TNeu defaultTNeuMD x (helper k)
  where
  helper :: Kind -> List.List TypeArg
  helper Type = List.Nil

  helper (KArrow k) = TypeArg defaultTypeArgMD (freshTHole unit) List.: (helper k)

setCursor :: CursorLocation -> State -> Maybe State
setCursor cursorLocation st = pure $ st { mode = makeCursorMode cursorLocation }
