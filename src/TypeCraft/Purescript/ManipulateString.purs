module TypeCraft.Purescript.ManipulateString where

import Data.Char
import Data.String
import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Debug (traceM)
import TypeCraft.Purescript.Key (Key)
import TypeCraft.Purescript.Util (hole, hole')

isLiteralChar :: String -> Boolean
isLiteralChar str = true

isIgnoreKey :: Key -> Boolean
isIgnoreKey key =
  (key.metaKey || key.altKey || key.ctrlKey)
    || ( key.key
          `Array.elem`
            [ "Tab"
            , "Enter"
            , "Escape"
            , "ArrowLeft"
            , "ArrowRight"
            , "ArrowUp"
            , "ArrowDown"
            ]
      )

manipulateString :: Key -> String -> Maybe String
manipulateString key str
  | isIgnoreKey key = Nothing
  | key.key == "Backspace" =
    if String.length str == 0 then
      Nothing
    else
      pure $ String.take (String.length str - 1) str
  | isLiteralChar key.key = pure (str <> key.key)
  | otherwise = Nothing
