module Test.TestCompletion where

import Data.Tuple.Nested (type (/\), (/\))
import Prelude
import Prim hiding (Type)
import Data.Foldable (traverse_)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Debug as Debug
import Effect (Effect)
import Effect.Class.Console as Console
import TypeCraft.Purescript.Completions (calculateCompletionGroups)
import TypeCraft.Purescript.Context (emptyAllContext)
import TypeCraft.Purescript.CursorMovement (getCursorChildren)
import TypeCraft.Purescript.Grammar (Term, Type)
import TypeCraft.Purescript.ModifyState (submitCompletion)
import TypeCraft.Purescript.State (Clipboard(..), Completion, CursorLocation(..), CursorMode, Mode(..), State, emptyQuery)

-- Tests all possible completions at every cursor location in the program.
testAllCompletions :: Term /\ Type -> Effect Unit
testAllCompletions (tm /\ ty) = do
  let
    toState :: CursorLocation -> State
    toState loc =
      { clipboard: EmptyClip
      , future: []
      , history: []
      , mode: CursorMode (toCursorMode loc)
      }

    toCursorMode :: CursorLocation -> CursorMode
    toCursorMode cursorLocation = { cursorLocation, query: emptyQuery }

    -- tests this cursor location, then recursively tests children cursor
    -- locations
    go :: CursorLocation -> Effect Unit
    go loc = do
      let
        st = toState loc

        complGroups = calculateCompletionGroups st (toCursorMode loc)
      flip traverse_ complGroups \{ completions } -> do
        flip traverse_ completions \k -> do
          let
            compl = k "x"
          testCompletion st compl
      traverse_ go
        $ List.filter case _ of
            TermCursor _ _ _ _ -> true
            InsideHoleCursor _ _ _ -> true
            _ -> false
        $ getCursorChildren loc

    locTop = TermCursor emptyAllContext ty Nil tm
  go locTop

testCompletion :: State -> Completion -> Effect Unit
testCompletion st compl = do
  case st.mode of
    CursorMode cursorMode -> case submitCompletion cursorMode compl of
      Nothing -> do
        Console.log "[✗] failure: `submitCompletion cursorMode compl ==> Nothing`"
        Console.log "cursorMode:"
        Debug.traceM cursorMode
        Console.log "compl:"
        Debug.traceM compl
      Just _ -> do
        Console.log "[✓] success"
    _ -> do
      Console.log "[✗] failure: `testCompletion st compl` expects that `st` has `CursorMode"
