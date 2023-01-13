module TypeCraft.Purescript.ManipulateString where

import Data.Char
import Data.String
import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Debug (traceM)

isNormalChar :: String -> Boolean
isNormalChar str = true

isIgnoreKey :: String -> Boolean
isIgnoreKey =
  ( _
      `Array.elem`
        [ "Tab"
        , "Enter"
        , "Meta"
        , "Shift"
        , "Escape"
        , "Alt"
        , "ArrowLeft"
        , "ArrowRight"
        , "ArrowUp"
        , "ArrowDown"
        ]
  )

manipulateString :: String -> String -> Maybe String
manipulateString key str
  | isIgnoreKey key = Nothing
  | key == "Backspace" = pure (String.take (String.length str - 1) str)
  | isNormalChar key = pure (str <> key)
  | otherwise = Nothing
