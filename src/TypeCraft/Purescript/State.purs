module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)

import Data.List (List(..))
import TypeCraft.Purescript.Context (AllContext, emptyAllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, Term(..), TermBind, Type(..), TypeArg, TypeBind, UpPath)

{-
This file will contain possible states for the editor
-}
-- state of the editor
type State
  = { mode :: Mode
    , history :: Array Mode
    }

data Mode
  = CursorMode
    { cursorLocation :: CursorLocation
    , query :: Query
    }
  | SelectMode Select

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
        { cursorLocation: TermCursor emptyAllContext (THole {} 0) Nil (Hole {})
        , query: emptyQuery
        }

data Clipboard
  = EmptyClip -- add more later, not priority yet

-- TODO: add more later, for now this is fine
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
