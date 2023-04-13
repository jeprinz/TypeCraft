module Test.TestCompletion where

import Prelude
import Prim hiding (Type)

import Data.Foldable (traverse_)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Class.Console as Console
import Effect.Exception.Unsafe (unsafeThrow)
import Test.Example.Example1 as Examples
import Test.Logging (logBlock, logSectionEnd, logSectionStart)
import TypeCraft.Purescript.Completions (calculateCompletionGroups)
import TypeCraft.Purescript.CursorMovement (getCursorChildren)
import TypeCraft.Purescript.Grammar (Term, Type)
import TypeCraft.Purescript.ModifyState (submitCompletion)
import TypeCraft.Purescript.State (Clipboard(..), Completion, CursorLocation(..), CursorMode, Mode(..), State, emptyQuery)
import TypeCraft.Purescript.Prelude (preludeContexts)

main :: Effect Unit
main =
  traverse_ testAllCompletions
    [ Examples.example1
    {- , Examples.example2 -}
    {-, Examples.example3 -}
    ]

-- testAllCompletions example2
-- Tests all possible completions at every cursor location in the program.
testAllCompletions :: Term /\ Type -> Effect Unit
testAllCompletions (tm /\ ty) = do
  logSectionStart "testAllCompletions"
  logBlock "term" (show tm)
  logBlock "type" (show ty)
  let
    toState :: CursorLocation -> State
    toState loc =
      { name: "program"
      , clipboard: EmptyClip
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

    locTop = TermCursor preludeContexts ty Nil tm
  go locTop

testCompletion :: State -> Completion -> Effect Unit
testCompletion st compl = do
  logSectionStart "testCompletion"
  case st.mode of
    CursorMode { cursorLocation: TermCursor _ctxs ty path tm } -> do
      logBlock "path" (show path)
      logBlock "term" (show tm)
      logBlock "type" (show ty)
    _ -> unsafeThrow $ "testCompletion: requires mode TermCursor, instead of actual mode: " <> show st.mode
  -- logBlock "state" (show st)
  logBlock "completion" (show compl)
  case st.mode of
    CursorMode cursorMode -> case submitCompletion cursorMode compl of
      Nothing -> do
        Console.log "[✗] failure: `submitCompletion cursorMode compl ==> Nothing`"
        logBlock "cursorMode" (show cursorMode)
      Just _ -> do
        Console.log "[✓] success"
    _ -> do
      Console.log "[✗] failure: `testCompletion st compl` expects that `st` has `CursorMode"
  logSectionEnd "testCompletion"
