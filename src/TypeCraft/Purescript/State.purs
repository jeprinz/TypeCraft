module TypeCraft.Purescript.State where

import Data.Tuple.Nested
import Data.Variant
import Prelude
import Prim hiding (Type)
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.List (List(..))
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Data.String as String
import Type.Proxy (Proxy(..))
import TypeCraft.Purescript.Context (AllContext, emptyAllContext)
import TypeCraft.Purescript.Grammar (Change, Constructor, CtrParam, Term(..), TermBind(..), Type(..), TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.MD (defaultAppMD, defaultArrowMD, defaultLambdaMD)
import TypeCraft.Purescript.ShallowEmbed (exampleProg1, exampleProg2, exampleProg3, exampleProg4, exampleProg5, exampleProg6)
import TypeCraft.Purescript.Unification (Sub)
import TypeCraft.Purescript.Util (hole, hole')

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
-- The Type and Context are at the type of the Term, regardless of root.
data Select
  = TermSelect {- cursor 1 -} UpPath AllContext Type Term {- cursor 2 -} UpPath AllContext Type Term {- orientation -} SelectOrientation
  | TypeSelect UpPath AllContext Type UpPath AllContext Type SelectOrientation
  | CtrListSelect UpPath AllContext (List Constructor) UpPath AllContext (List Constructor) SelectOrientation
  | CtrParamListSelect UpPath AllContext (List CtrParam) UpPath AllContext (List CtrParam) SelectOrientation
  | TypeArgListSelect UpPath AllContext (List TypeArg) UpPath AllContext (List TypeArg) SelectOrientation
  | TypeBindListSelect UpPath AllContext (List TypeBind) UpPath AllContext (List TypeBind) SelectOrientation

type SelectOrientation
  = Variant ( top :: Unit, bot :: Unit )

topSelectOrientation :: SelectOrientation
topSelectOrientation = inj (Proxy :: Proxy "top") unit

botSelectOrientation :: SelectOrientation
botSelectOrientation = inj (Proxy :: Proxy "bot") unit

derive instance genericSelect :: Generic Select _

instance showSelect :: Show Select where
  show x = genericShow x

selectToCursorLocation :: Select -> CursorLocation
selectToCursorLocation = case _ of
  TermSelect tmPath1 ctxs1 ty1 tm1 tmPath2 ctxs2 ty2 tm2 ori ->
    (ori # _) <<< (case_ # _) <<< onMatch
      $ { top: const $ TermCursor ctxs1 ty1 tmPath1 tm1
        , bot: const $ TermCursor ctxs2 ty2 (tmPath2 <> tmPath1) tm2
        }
  _ -> hole' "selectToCursorLocation: other cases"

cursorLocationToSelect :: SelectOrientation -> CursorLocation -> Select
cursorLocationToSelect ori = case _ of
  TermCursor ctxs ty tmPath tm -> TermSelect tmPath ctxs ty tm Nil ctxs ty tm ori
  _ -> hole' "cursorLocationToSelect: other cases"
