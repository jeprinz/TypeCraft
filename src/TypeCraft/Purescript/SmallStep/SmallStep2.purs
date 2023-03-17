module TypeCraft.Purescript.SmallStep.SmallStep where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import Data.UUID (UUID)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.SmallStep.UTerm
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested
import Data.Map (Map)
import Data.Map as Map
import Data.List as List
import Data.Traversable (sequence)
import TypeCraft.Purescript.Util (union', lookup')
import Data.Either (Either(..))
import Data.Tuple (fst, snd)
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util

type TyCtxCh = CAllContext /\ Change

termRules :: Label -> TyCtxCh -> List TyCtxCh
termRules _ _ = hole' "termRules"

toothRules :: Label -> TyCtxCh -> TyCtxCh /\ List TyCtxCh /\ List TyCtxCh
toothRules _ _ = hole' "toothRules"