module TypeCraft.Purescript.Util where

import Prelude
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Map (Map, lookup)
import Data.Maybe (Maybe(..))

hole :: forall a. a
hole = unsafeThrow "hole"

hole' :: forall a. String -> a
hole' label = unsafeThrow $ "hole: " <> label

lookup' :: forall k v. Ord k => k -> Map k v -> v
lookup' x m = case lookup x m of
  Just v -> v
  Nothing -> unsafeThrow "lookup failed"
