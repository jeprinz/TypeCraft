module TypeCraft.Purescript.Nullable where

import Prelude

import Data.Maybe (Maybe, maybe)

foreign import data Nullable :: Type -> Type

foreign import emptyNullable :: forall a. Nullable a

foreign import pureNullable :: forall a. a -> Nullable a

fromMaybe :: forall a. Maybe a -> Nullable a
fromMaybe = maybe emptyNullable pureNullable
