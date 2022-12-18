module TypeCraft.Purescript.Kinds where

import Prelude
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))

{-
Operations on kinds
-}

bindsToKind :: List TypeBind -> Kind
bindsToKind Nil = Type
bindsToKind (_ : binds) = KArrow (bindsToKind binds)
