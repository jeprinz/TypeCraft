module Test.Example.State1 where

import Prim hiding (Type)
import Data.UUID as UUID
import Data.Map as Map
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.Grammar (Term(..), Type(..))
import TypeCraft.Purescript.Util (fromJust)

example1 :: Term /\ Type
example1 =
  (Hole {})
    /\ (THole {} (fromJust (UUID.parseUUID "9c8e3cf3-7186-4bee-aecd-ca354343f0ea")) (Set.fromFoldable []) (Map.fromFoldable []))

-- example2 :: Term /\ Type