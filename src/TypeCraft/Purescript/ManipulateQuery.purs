module TypeCraft.Purescript.ManipulateQuery where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Unification

import Control.Monad.Writer as Writer
import Data.Array (any)
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.String as String
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID (UUID)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Change(..), PolyType(..), Term(..), TermVarID, Tooth(..), Type(..), TypeArg(..), TypeHoleID, TypeVarID, freshHole, freshTHole, freshTermBind, freshTypeBind, tyInject)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.MD (defaultAppMD, defaultArrowMD, defaultBufferMD, defaultLambdaMD, defaultLetMD, defaultTLetMD, defaultTypeBoundaryMD, defaultVarMD)
import TypeCraft.Purescript.ManipulateString (manipulateString)
import TypeCraft.Purescript.State (Completion(..), CursorLocation(..), CursorMode, Query, State)
import TypeCraft.Purescript.Util (hole)

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
kindaStartsWith str pre =
  and
    [ String.length str > 0 -- string can't be empty
    , String.length pre > 0 -- prefix can't be empty
    , isJust $ String.stripPrefix (String.Pattern (String.take (String.length str) pre)) str
    ]

kindaStartsWithAny :: String -> Array String -> Boolean
kindaStartsWithAny str pres =
  and
    [ String.length str > 0 -- string can't be empty
    , any (isJust <<< \pre -> String.stripPrefix (String.Pattern (String.take (String.length str) pre)) str) pres
    ]

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
                  Right (tm' /\ sub) -> Writer.tell [ [ CompletionTerm tm' sub{subTypeVars = Map.empty} ] ] -- TODO: Jacob: why would there be subTypeVars here anyway? I'm confused about that. Isn't unification for holes?
        )
        (Map.toUnfoldable ctxs.mdctx :: Array (UUID /\ String))
      -- Lambda
      when (str `kindaStartsWithAny` [ "lam", "\\" ])
        $ Writer.tell
            [ [ let
                  alpha = freshTHole unit
                in
                  CompletionTermPath -- lam (~ : alpha) ↦ ({} : ty)
                    (List.singleton $ Lambda3 defaultLambdaMD (freshTermBind Nothing) alpha ty)
                    (Plus alpha (tyInject ty))
              ]
            ]
      -- Let
      when (str `kindaStartsWith` "let")
        $ Writer.tell
            [ [ CompletionTermPath -- let ~<∅> : alpha = ? in {} : ty
                  (List.singleton $ Let5 defaultLetMD (freshTermBind Nothing) List.Nil (freshHole unit) (freshTHole unit) ty)
                  (tyInject ty)
              ]
            ]
      -- App
      when (str `kindaStartsWithAny` [ " ", "$" ]) $
        case ty of -- TODO: should really be if the type UNIFIES with an Arrow, instead of IS an arrow...
            Arrow _ ty1 ty2 ->
                Writer.tell
                    [ [ CompletionTermPath -- ({} ?)
                          (List.singleton $ App1 defaultAppMD (freshHole unit) ty1 ty2)
                          (Minus ty1 (tyInject ty2))
                      ]
                    ]
            _ -> pure unit
      -- TLet
      when (str `kindaStartsWith` "tlet")
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ TLet4 defaultTLetMD (freshTypeBind Nothing) List.Nil (freshTHole unit) ty)
                  (tyInject ty)
              ]
            ]
      -- TypeBoundary
      when (str `kindaStartsWithAny` [ "{}", "boundary" ])
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ TypeBoundary1 defaultTypeBoundaryMD (tyInject ty))
                  (tyInject ty)
              ]
            ]
      -- Hole
      when (str `kindaStartsWithAny` [ "hole", "?" ])
        $ Writer.tell
            [ [ CompletionTerm
                  (freshHole unit)
--                  ty
                  {subTypeVars: Map.empty, subTHoles: Map.empty}
              ]
            ]
      -- Buffer
      when (str `kindaStartsWithAny` [ "buffer", "#" ])
        $ Writer.tell
            [ [ CompletionTermPath
                  (List.singleton $ Buffer3 defaultBufferMD (freshHole unit) (freshTHole unit) ty)
                  (tyInject ty)
              ]
            ]
  TypeCursor ctxs path ty ->
    Writer.execWriter do
      -- TNeu
      -- TODO: TNeu
      -- Arrow
      when (str `kindaStartsWithAny` [ "arrow", "->" ])
        $ Writer.tell
            [ [ let
                  thole = freshTHole unit
                in
                  CompletionTypePath
                    (List.singleton $ Arrow2 defaultArrowMD thole)
                    (Plus thole (tyInject ty))
              ]
            ]
      -- THole
      when (str `kindaStartsWithAny` [ "hole", "?" ])
        $ Writer.tell
            [ [ CompletionType (freshTHole unit)
              ]
            ]
  _ -> [] -- TODO: impl