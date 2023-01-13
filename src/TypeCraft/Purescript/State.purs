module TypeCraft.Purescript.State where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Show.Generic (genericShow)
import TypeCraft.Purescript.Context (AllContext, emptyAllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, Term(..), TermBind(..), Type(..), TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.MD (defaultAppMD, defaultArrowMD, defaultLambdaMD)
import TypeCraft.Purescript.ShallowEmbed (exampleProg2, exampleProg3, exampleProg4, exampleProg5, exampleProg6)
import TypeCraft.Purescript.Util (hole)

{-
This file will contain possible states for the editor
-}
-- state of the editor
type State
  = { mode :: Mode
    , history :: Array Mode
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
    , completion_i :: Int
    , completionOption_i :: Int
    }

emptyQuery :: Query
emptyQuery =
  { string: ""
  , completion_i: 0
  , completionOption_i: 0
  }

makeCursorMode :: CursorLocation -> Mode
makeCursorMode cursorLocation =
  CursorMode
    { cursorLocation
    , query: emptyQuery
    }

makeState :: Mode -> State
makeState mode =
  { mode
  , history: []
  }

initState :: State
initState =
  makeState
    $ CursorMode
        { cursorLocation: TermCursor emptyAllContext ty Nil tm
        , query: emptyQuery
        }
  where
  ty /\ tm = exampleProg5

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
The TypeContext, TermContext, and Type are understood as being inside the second path.
e.g. if the term selection is  path1[path2[term]], then the contexts and type given are for inside path2 and outside term.
-}
-- Boolean is true if root is at top, false if at bottom. The Type and Context
-- are at thte type of the Term, regardless of root.
data Select
  = TermSelect AllContext Boolean Type UpPath UpPath Term
  | TypeSelect AllContext Boolean UpPath UpPath Type
  | CtrListSelect AllContext Boolean UpPath UpPath (List Constructor)
  | CtrParamListSelect AllContext Boolean UpPath UpPath (List CtrParam)
  | TypeArgListSelect AllContext Boolean UpPath UpPath (List TypeArg)
  | TypeBindListSelect AllContext Boolean UpPath UpPath (List TypeBind)

derive instance genericSelect :: Generic Select _

instance showSelect :: Show Select where
  show x = genericShow x
