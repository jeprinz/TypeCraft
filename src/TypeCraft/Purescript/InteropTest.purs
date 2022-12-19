module TypeCraft.Purescript.InteropTest where

import Prelude

foreign import data TestType :: Type

foreign import makeTestType :: String -> TestType

intToTestType :: Int -> TestType
intToTestType x = makeTestType ("int: " <> show x)
