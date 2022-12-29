module TypeCraft.Purescript.State where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.TermRec (TermRecValue)
import TypeCraft.Purescript.TermRec (recTerm)
import TypeCraft.Purescript.TermRec (TypeRecValue)
import TypeCraft.Purescript.PathRec
import Data.Maybe (Maybe)
import Data.Maybe (Maybe(..))
import Data.List (length)
import Data.List (index)

{-
This file will contain possible states for the editor
-}

-- state of the editor
type State = {
        mode :: Mode
    }

data Mode 
    = CursorMode {
            cursorLocation :: CursorLocation,
            query :: Query
        }
    | SelectMode Select

type Query = {
        string :: String,
        completion_i :: Int,
        completionOption_i :: Int
    }

emptyQuery :: Query
emptyQuery =
    { string: ""
    , completion_i: 0
    , completionOption_i: 0
    }

initCursorMode :: CursorLocation -> Mode
initCursorMode cursorLocation = CursorMode 
    { cursorLocation
    , query: emptyQuery
    }

initState :: Mode -> State
initState mode = 
    { mode
    }

data Clipboard = EmptyClip -- add more later, not priority yet

data CursorLocation
    = TermCursor AllContext MDType Type UpPath Term
    | TypeCursor AllContext UpPath Type -- add more later, for now this is fine
--    | CtrCursor AllContext UpPath Constructor
--    | CtrParamCursor AllContext UpPath CtrParam
--    | TypeArgCursor AllContext UpPath TypeArg
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
data Select
    = TermSelect AllContext Type Boolean UpPath UpPath Term -- Boolean is true if root is at top, false if at bottom. The Type and Context are at thte type of the Term, regardless of root.
    | TypeSelect AllContext UpPath UpPath Type
    | CtrListSelect AllContext UpPath UpPath (List Constructor)
    | CtrParamListSelect AllContext UpPath UpPath (List CtrParam)
    | TypeArgListSelect AllContext UpPath UpPath (List TypeArg)
    | TypeBindListSelect AllContext UpPath UpPath (List TypeBind)