module TypeCraft.Purescript.Util where

import Prelude
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Map (Map, lookup, member, delete)
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

justWhen :: forall a. Boolean -> (Unit -> a) -> Maybe a 
justWhen false _ = Nothing
justWhen true k = Just (k unit)

delete' :: forall v k . Ord k => k -> Map k v -> Map k v
--delete' k m  = if member k m then delete k m else unsafeThrow "Tried to delete an element not present in the map"
delete' k m  = delete k m
