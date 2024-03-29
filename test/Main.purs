module Test.Main where

import Prelude
import TypeCraft.Purescript.State

import Data.Maybe (Maybe(..))
import Debug as Debug
import Effect (Effect)
import Effect.Class.Console as Console
import Effect.Exception.Unsafe (unsafeThrow)
import Test.TestCompletion as TestCompletion
import TypeCraft.Purescript.ModifyState (submitCompletion)

main :: Effect Unit
main = do 
  TestCompletion.main
