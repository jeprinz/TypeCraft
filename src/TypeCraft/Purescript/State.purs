module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)

import Data.Argonaut (class DecodeJson, class EncodeJson, encodeJson)
import Data.Argonaut.Decode.Generic (genericDecodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.Tuple.Nested ((/\))
import TypeCraft.Purescript.Alpha (Sub)
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Change, Constructor, CtrParam, ListCtrChange, ListCtrParamChange, ListTypeBindChange, Term, TermBind, Type, TypeBind, UpPath)
import TypeCraft.Purescript.ShallowEmbed (exampleProg1)
import TypeCraft.Purescript.Prelude (preludeContexts)

{-
This file will contain possible states for the editor
-}
-- state of the editor
type State
  = { name :: String
    , mode :: Mode
    , clipboard :: Clipboard
    , history :: Array Mode
    , future :: Array Mode
    }

data Mode
  = CursorMode CursorMode
  | SelectMode SelectMode

type CursorMode
  = { cursorLocation :: CursorLocation
    , query :: Query
    }

type SelectMode
  = { select :: Select
    }

derive instance genericMode :: Generic Mode _

instance showMode :: Show Mode where
  show x = genericShow x

type Query
  = { string :: String
    , completionGroup_i :: Int
    , completionGroupItem_i :: Int
    , completionGroups :: Array (Array Completion)
    }

isEmptyQuery :: Query -> Boolean
isEmptyQuery { string } = String.null string

-- TODO: completions for other syntax kinds
data Completion
  = CompletionTerm Term Sub -- NOTE: the term should not already have the sub applied
  | CompletionTermPath UpPath Change Sub
  -- | CompletionTermPath2 UpPath (Unit -> CursorLocation) -- A more generic version of a completion
  | CompletionType Type Sub
  | CompletionTypePath UpPath Change
  | CompletionCtrListPath UpPath ListCtrChange
  | CompletionCtrParamListPath UpPath ListCtrParamChange
  | CompletionTypeBindListPath UpPath ListTypeBindChange

derive instance genericCompletion :: Generic Completion _

instance showCompletion :: Show Completion where
  show x = genericShow x

emptyQuery :: Query
emptyQuery =
  { string: ""
  , completionGroup_i: 0
  , completionGroupItem_i: 0
  , completionGroups: []
  }

getCompletion :: Query -> Maybe Completion
getCompletion query = do
  cmpls <- query.completionGroups Array.!! (query.completionGroup_i `mod` Array.length query.completionGroups)
  cmpls Array.!! (query.completionGroupItem_i `mod` Array.length cmpls)

makeCursorMode :: CursorLocation -> Mode
makeCursorMode cursorLocation =
  CursorMode
    { cursorLocation
    , query: emptyQuery
    }

makeSelectMode :: Select -> Mode
makeSelectMode select = SelectMode { select }

initState :: State
initState =
  { name: "program"
  , mode
  , clipboard: EmptyClip
  , history: [ mode ]
  , future: []
  }
  where
  ty /\ tm = exampleProg1

  mode =
    CursorMode
      { cursorLocation: TermCursor preludeContexts ty Nil tm
      , query: emptyQuery
      }

data Clipboard
  = EmptyClip -- add more later, not priority yet
  -- Term clipboards:
  | TermClip AllContext Type Term
  | TypeClip AllContext Type
  | VarNameClip String -- both for TermBind and TypeBind
  -- Path clipboards:
  | TermPathClip AllContext Type UpPath AllContext Type
  | TypePathClip AllContext UpPath
  | CtrListClip AllContext UpPath -- technically doesn't need term contexts but whatever
  | CtrParamList AllContext UpPath -- technically doesn't need term contexts but whatever
  --  | TypeArgList AllContext UpPath -- technically doesn't need term contexts but whatever
  | VarNameList AllContext UpPath -- for TypeBind Lists

derive instance genericClipboard :: Generic Clipboard _

instance showClipboard :: Show Clipboard where
  show x = genericShow x

data CursorLocation
  = TermCursor AllContext Type UpPath Term
  | TypeCursor AllContext UpPath Type
  --   | CtrCursor AllContext UpPath Constructor
  --   | CtrParamCursor AllContext UpPath CtrParam
  --   | TypeArgCursor AllContext UpPath TypeArg
  | TypeBindCursor AllContext UpPath TypeBind
  | TermBindCursor AllContext UpPath TermBind
  | CtrListCursor AllContext UpPath (List Constructor)
  | CtrParamListCursor AllContext UpPath (List CtrParam)
  --  | TypeArgListCursor AllContext UpPath (List TypeArg)
  | TypeBindListCursor AllContext UpPath (List TypeBind)
  | InsideHoleCursor AllContext Type UpPath

derive instance genericCursorLocation :: Generic CursorLocation _

instance showCursorLocation :: Show CursorLocation where
  show x = genericShow x

{-
Each Select mode consists of essentially two cursors:
Select = Path      = topPath                                                        \
       x Context   = context underneath topPath                                     | - Cursor 1
       x Term      = middlePath [bottomTerm]                                        /
       x Path      = middlePath                                                     \
       x Context   = context underneath topPath <> middlePath                       | - Cursor 2
       x Term      = bottomTerm                                                     /
       x Boolean   = where the root is: true if at top, false if at bottom

This state represents a program that looks like this:
topPath [middlePath [bottomTerm]]

Note that TermSelect in particular also has a Type wherever there is a context, which is the type at that point.
-}
-- The Type and Context are at the type of the Term, regardless of root.
data Select
  = TermSelect {- cursor 1 -} UpPath AllContext Type Term {- cursor 2 -} UpPath AllContext Type Term {- orientation -} SelectOrientation
  | TypeSelect UpPath AllContext Type UpPath AllContext Type SelectOrientation
  | CtrListSelect UpPath AllContext (List Constructor) UpPath AllContext (List Constructor) SelectOrientation
  | CtrParamListSelect UpPath AllContext (List CtrParam) UpPath AllContext (List CtrParam) SelectOrientation
  --  | TypeArgListSelect UpPath AllContext (List TypeArg) UpPath AllContext (List TypeArg) SelectOrientation
  | TypeBindListSelect UpPath AllContext (List TypeBind) UpPath AllContext (List TypeBind) SelectOrientation

type SelectOrientation
  = Boolean -- I didn't know how to match on a Variant, so I changed it back to a boolean. That way I can use an if expression like a normal person

topSelectOrientation :: Boolean -- the root of the seledction is at the top, so the bottom moves with shift-arrow keys
topSelectOrientation = true

botSelectOrientation :: Boolean -- the root of the selection is at the bottom, so the top moves with shift-arrow keys
botSelectOrientation = false

derive instance genericSelect :: Generic Select _

instance showSelect :: Show Select where
  show x = genericShow x

selectToCursorLocation :: Select -> CursorLocation
selectToCursorLocation = case _ of
  TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori ->
    if ori then
      TermCursor ctxs2 ty2 (tmPath2 <> tmPath1) tm2
    else
      TermCursor ctxs1 ty1 tmPath1 tm1
  TypeSelect path1 ctxs1 ty1 path2 ctxs2 ty2 ori ->
    if ori then
      TypeCursor ctxs2 (path2 <> path1) ty2
    else
      TypeCursor ctxs1 path1 ty1
  CtrListSelect path1 ctxs1 ctrs1 path2 ctxs2 ctrs2 ori ->
    if ori then
      CtrListCursor ctxs2 (path2 <> path1) ctrs2
    else
      CtrListCursor ctxs1 path1 ctrs1
  CtrParamListSelect path1 ctxs1 ctrParams1 path2 ctxs2 ctrParams2 ori ->
    if ori then
      CtrParamListCursor ctxs2 (path2 <> path1) ctrParams2
    else
      CtrParamListCursor ctxs1 path1 ctrParams1
  TypeBindListSelect path1 ctxs1 tyBinds1 path2 ctxs2 tyBinds2 ori ->
    if ori then
      TypeBindListCursor ctxs2 (path2 <> path1) tyBinds2
    else
      TypeBindListCursor ctxs1 path1 tyBinds1


type Program = {
  name :: String,
  type_:: Type,
  term:: Term
}

-- derive instance genericProgram :: Generic Program _
-- instance encodeProgram :: EncodeJson Program where encodeJson x = genericEncodeJson x
-- instance decodeProgram :: DecodeJson Program where decodeJson x = genericDecodeJson x