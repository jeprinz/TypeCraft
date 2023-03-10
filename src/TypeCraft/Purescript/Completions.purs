module TypeCraft.Purescript.Completions where

import Prelude
import Prim hiding (Type)

import Control.Monad.Writer as Writer
import Data.Array (any)
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import Data.List (List(..))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.String as String
import Data.String.Regex as Regex
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID (UUID)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Alpha (emptySub)
import TypeCraft.Purescript.ChangeTerm (chCtrList, chParamList, chTypeBindList)
import TypeCraft.Purescript.Context (kCtxInject)
import TypeCraft.Purescript.Grammar (Change(..), Constructor(..), CtrParam(..), Kind(..), ListCtrChange(..), ListCtrParamChange(..), ListTypeBindChange(..), Tooth(..), Type(..), TypeArg(..), TypeVar(..), TypeVarID, freshHole, freshTHole, freshTermBind, freshTypeBind, tyInject)
import TypeCraft.Purescript.MD (defaultAppMD, defaultArrowMD, defaultBufferMD, defaultCtrMD, defaultCtrParamMD, defaultGADTMD, defaultLambdaMD, defaultLetMD, defaultTLetMD, defaultTNeuMD, defaultTypeArgMD, defaultTypeBoundaryMD)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, State)
import TypeCraft.Purescript.Unification (fillNeutral, runUnify, unify)
import Debug (trace)

type CompletionGroup
  = { filterLabel :: String -> Boolean
    , completions :: Array (String -> Completion)
    }

calculateCompletionGroups :: State -> CursorMode -> List CompletionGroup
calculateCompletionGroups _st cursorMode = case cursorMode.cursorLocation of
  InsideHoleCursor ctxs ty _path -> 
    Writer.execWriter do
      -- fill with neutral form
      traverse_
        ( \(id /\ varName) -> case Map.lookup id ctxs.ctx of
            Nothing -> unsafeThrow $ "the entry '" <> show (id /\ varName) <> "' was found in the ctxs.mdctx, but not in the ctxs.ctx: '" <> show ctxs.ctx <> "'"
            Just pty -> do
              -- when (str `kindaStartsWith` varName) do
              case runUnify (fillNeutral ctxs.actx pty id ty) of
                Left _msg -> pure unit
                -- TODO: Jacob: why would there be subTypeVars here anyway? I'm confused about that. Isn't unification for holes?
                Right (tm' /\ sub) ->
                  Writer.tell <<< List.fromFoldable $
                    [ { filterLabel: (_ `kindaStartsWithAny` [ varName ])
                      , completions: [ const $ CompletionTerm tm' sub ]
                      }
                    ]
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (_ /\ _)) 
  TermCursor _ctxs ty _path _tm ->
    Writer.execWriter do
      -- en-lambda
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "lambda", "\\" ])
          , completions:
              [ const
                  let
                    alpha = freshTHole unit

                    tmBind = freshTermBind Nothing
                  in
                    CompletionTermPath -- lam (~ : alpha) ↦ ({} : ty)
                      (List.singleton $ Lambda3 defaultLambdaMD tmBind alpha ty)
                      (Plus alpha (tyInject ty))
                      emptySub
              ]
          }
        ]
      -- en-let
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "let", "def" ])
          , completions:
              [ const
                  $ CompletionTermPath -- let ~<∅> : ? = ? in {} : ty
                      (List.singleton $ Let5 defaultLetMD (freshTermBind Nothing) List.Nil (freshHole unit) (freshTHole unit) ty)
                      (tyInject ty)
                      emptySub
              , const
                  $ CompletionTermPath -- let ~<∅> : ? = {} in ? : ty
                      (List.singleton $ Let3 defaultLetMD (freshTermBind Nothing) List.Nil ty (freshHole unit) ty)
                      (tyInject ty)
                      emptySub
              ]
          }
        ]
      -- en-app
      do
        let
          alpha = freshTHole unit
          beta = freshTHole unit
        case runUnify (unify (Arrow defaultArrowMD alpha beta) ty) of
          Left _ -> pure unit
          Right (Arrow _md ty1 ty2 /\ sub) ->
--            trace ("Here we are. ty is: " <> show ty <> " and ty1 is " <> show ty1 <> " and ty2 is " <> show ty2) \_ ->
            Writer.tell <<< List.fromFoldable $
              [ { filterLabel: (_ `kindaStartsWithAny` [ " ", "$" ])
                , completions:
                    [ const
                        $ CompletionTermPath -- ({} ?)
                            (List.singleton $ App1 defaultAppMD (freshHole unit) ty1 ty2)
                            (Minus ty1 (tyInject ty2))
                            emptySub {-sub-}
                    ]
                }
              ]
          Right _ -> unsafeThrow "impossible; type must be an arrow after unifying with arrow"
      -- en-alias
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "alias", "tlet", "tdef" ])
          , completions:
              [ const
                  $ CompletionTermPath
                      (List.singleton $ TLet4 defaultTLetMD (freshTypeBind Nothing) List.Nil (freshTHole unit) ty)
                      (tyInject ty)
                      emptySub
              ]
          }
        ]
      -- en-data
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "data" ])
          , completions:
              [ const
                  $ CompletionTermPath
                      (List.singleton $ Data4 defaultGADTMD (freshTypeBind Nothing) List.Nil List.Nil ty)
                      (tyInject ty)
                      emptySub
              ]
          }
        ]
      -- en-type-boundary
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "{" ])
          , completions:
              [ const
                  $ CompletionTermPath
                      (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (tyInject ty))
                      (tyInject ty)
                      emptySub
              ]
          }
        ]
      -- en-buffer
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "buf", "#" ])
          , completions:
              [ const
                  $ CompletionTermPath
                      (List.singleton $ Buffer3 defaultBufferMD (freshHole unit) (freshTHole unit) ty)
                      (tyInject ty)
                      emptySub
              ]
          }
        ]
  TypeCursor ctxs _path ty ->
    Writer.execWriter do
      traverse_
        ( \(id /\ tyName) -> case Map.lookup id ctxs.kctx of
            Nothing -> unsafeThrow $ "the entry '" <> show (id /\ tyName) <> "' was found in the ctxs.mdkctx, but not in the ctxs.kctx: '" <> show ctxs.ctx <> "'"
            Just kind -> case ty of
              THole _md x _weakenings _ -> do
                let
                  cTy = makeEmptyTNeu id kind
                Writer.tell <<< List.fromFoldable $
                  [ { filterLabel: (_ `kindaStartsWithAny` [ tyName ])
                    , completions: [ const $ CompletionType cTy { subTypeVars: Map.empty, subTHoles: Map.insert x cTy Map.empty } ]
                    }
                  ]
              _ -> pure unit
        )
        (Map.toUnfoldable ctxs.mdkctx :: Array (_ /\ _))
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "->" ])
          , completions:
              [ const
                  $ let
                      thole = freshTHole unit
                    in
                      CompletionTypePath
                        (List.singleton $ Arrow2 defaultArrowMD thole)
                        (Plus thole (tyInject ty))
              ]
          }
        ]
  TypeBindListCursor _ctxs _path tyBinds ->
    Writer.execWriter do
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ " ", "," ])
          , completions:
              [ const
                  let
                    newTyBind = (freshTypeBind Nothing)
                  in
                    CompletionTypeBindListPath (List.singleton $ TypeBindListCons2 newTyBind) (ListTypeBindChangePlus newTyBind (chTypeBindList tyBinds))
              ]
          }
        ]
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: isValidTypeBindLabel
          , completions:
              [ \str ->
                  let
                    newTyBind = freshTypeBind (Just str)
                  in
                    CompletionTypeBindListPath (List.singleton $ TypeBindListCons2 newTyBind) (ListTypeBindChangePlus newTyBind (chTypeBindList tyBinds))
              ]
          }
        ]
  CtrListCursor ctxs _path ctrs ->
    Writer.execWriter do
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ "|" ])
          , completions:
              [ const
                  let
                    kctx = kCtxInject ctxs.kctx ctxs.actx

                    ctrCh = fst (chCtrList kctx ctrs)

                    newCtr = (Constructor defaultCtrMD (freshTermBind Nothing) List.Nil)
                  in
                    CompletionCtrListPath (List.singleton $ CtrListCons2 newCtr)
                      (ListCtrChangePlus newCtr ctrCh)
              ]
          }
        ]
  CtrParamListCursor ctxs _path ctrParams ->
    Writer.execWriter do
      Writer.tell <<< List.fromFoldable $
        [ { filterLabel: (_ `kindaStartsWithAny` [ " ", "," ])
          , completions:
              [ const
                  let
                    kctx = kCtxInject ctxs.kctx ctxs.actx

                    ctrParamCh = fst (chParamList kctx ctrParams)

                    newCtrParam = (CtrParam defaultCtrParamMD (freshTHole unit))
                  in
                    CompletionCtrParamListPath (List.singleton $ CtrParamListCons2 newCtrParam)
                      (ListCtrParamChangePlus newCtrParam ctrParamCh)
              ]
          }
        ]
  _ -> Nil

makeEmptyTNeu :: TypeVarID -> Kind -> Type
makeEmptyTNeu x k = TNeu defaultTNeuMD (TypeVar x) (helper k)
  where
  helper :: Kind -> List.List TypeArg
  helper Type = List.Nil

  helper (KArrow k') = TypeArg defaultTypeArgMD (freshTHole unit) List.: (helper k')

kindaStartsWith :: String -> String -> Boolean
kindaStartsWith str pat =
  and
    [ len_str > 0 -- string can't be empty
    , len_pat > 0 -- prefix can't be empty
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
