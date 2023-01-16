module TypeCraft.Purescript.Util where

import Prelude
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Map (Map, lookup)
import Data.Maybe (Maybe(..))
import Data.List(List, head)

hole :: forall a. a
hole = unsafeThrow "hole"

hole' :: forall a. String -> a
hole' label = unsafeThrow $ "hole: " <> label

lookup' :: forall k v. Ord k => k -> Map k v -> v
lookup' x m = case lookup x m of
  Just v -> v
  Nothing -> unsafeThrow "lookup failed"

head' :: forall a . List a -> a
head' l = case head l of
    Nothing -> unsafeThrow "head failed"
    Just a -> a

fromJust :: forall a . Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = unsafeThrow "fromJust failed"

fromJust' :: forall a . String -> Maybe a -> a
fromJust' _ (Just x) = x
fromJust' msg Nothing = unsafeThrow $ "fromJust failed: " <> msg