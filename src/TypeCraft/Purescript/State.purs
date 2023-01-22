module TypeCraft.Purescript.State where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Data.String as String
import TypeCraft.Purescript.Context (AllContext, emptyAllContext)
import TypeCraft.Purescript.Grammar (Change, Constructor, CtrParam, Term(..), TermBind(..), Type(..), TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.MD (defaultAppMD, defaultArrowMD, defaultLambdaMD)
import TypeCraft.Purescript.ShallowEmbed (exampleProg1, exampleProg2, exampleProg3, exampleProg4, exampleProg5, exampleProg6)
import TypeCraft.Purescript.Unification (Sub)
import TypeCraft.Purescript.Util (hole)

{-
This file will contain possible states for the editor
-}
-- state of the editor
type State
  = { mode :: Mode
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
  = CompletionTerm Term {-Type-} Sub -- I don't think we need a Type here? Aren't terms only filled when they are the correct type up to unification? (Or if not, at least make it a typechange?)
  | CompletionTermPath UpPath Change
  | CompletionType Type
  | CompletionTypePath UpPath Change

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
  { mode
  , history: [ mode ]
  , future: []
  }
  where
  ty /\ tm = exampleProg1

  mode =
    CursorMode
      { cursorLocation: TermCursor emptyAllContext ty Nil tm
      , query: emptyQuery
      }

data Clipboard
  = EmptyClip -- add more later, not priority yet

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
  | TypeArgListCursor AllContext UpPath (List TypeArg)
  | TypeBindListCursor AllContext UpPath (List TypeBind)

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
-- Boolean is true if root is at top, false if at bottom. The Type and Context
-- are at thte type of the Term, regardless of root.
data Select
  = TermSelect UpPath AllContext Type Term UpPath AllContext Type Term Boolean
  --             <-------Cursor 1----------> <-----Cursor 2------------>
  | TypeSelect UpPath AllContext Type UpPath AllContext Type Boolean
  | CtrListSelect UpPath AllContext (List Constructor) UpPath AllContext (List Constructor) Boolean
  | CtrParamListSelect UpPath AllContext (List CtrParam) UpPath AllContext (List CtrParam) Boolean
  | TypeArgListSelect UpPath AllContext (List TypeArg) UpPath AllContext (List TypeArg) Boolean
  | TypeBindListSelect UpPath AllContext (List TypeBind) UpPath AllContext (List TypeBind) Boolean

derive instance genericSelect :: Generic Select _

instance showSelect :: Show Select where
  show x = genericShow x
