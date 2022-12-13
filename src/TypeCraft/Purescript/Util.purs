module TypeCraft.Purescript.Util where

import Prelude
import Effect.Exception.Unsafe (unsafeThrow)

hole :: forall a. a
hole = unsafeThrow "hole"
