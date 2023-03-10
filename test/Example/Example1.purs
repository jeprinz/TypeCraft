module Test.Example.State1 where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import Data.List (List(..))
import Data.Map as Map
import Data.Set as Set
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID as UUID
import TypeCraft.Purescript.Util (fromJust)

example1 :: Term /\ Type
example1 =
  (Hole {})
    /\ (THole {} (TypeHoleID <<< fromJust $ UUID.parseUUID "9c8e3cf3-7186-4bee-aecd-ca354343f0ea") (Set.fromFoldable []) (Map.fromFoldable []))

example2 :: Term /\ Type
example2 =
  (Let { bodyIndented: true, defIndented: false, typeIndented: false, varIndented: false } (TermBind { varName: "" } (TermVarID <<< fromJust $ UUID.parseUUID "10a74b7c-3df3-4e3b-b4ad-b1604a75000b")) Nil (Hole {}) (THole {} (TypeHoleID <<< fromJust $ UUID.parseUUID "02355002-f3fd-4e8c-94bd-0a7aaef884a0") (Set.fromFoldable []) (Map.fromFoldable [])) (Hole {}) (THole {} (TypeHoleID <<< fromJust $ UUID.parseUUID "104261b2-a21e-45f4-bc86-c51e27c856f6") (Set.fromFoldable []) (Map.fromFoldable [])))
    /\ (THole {} (TypeHoleID <<< fromJust $ UUID.parseUUID "104261b2-a21e-45f4-bc86-c51e27c856f6") (Set.fromFoldable []) (Map.fromFoldable []))
