module TypeCraft.Purescript.Dentist where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (hole)
import Data.List(List(..), (:))

-- Code pertaining to teeth

combineToothTerm :: Tooth -> Term -> Term
combineToothTerm _ _ = hole

combineDownPathTerm :: DownPath -> Term -> Term
combineDownPathTerm = hole

combineToothType :: Tooth -> Type -> Type
combineToothType _ _ = hole

{-
Issue: there are e.g. type teeth which go from type to term, e.g. in the
annotation of a lambda.
-}

class ToothAppendable syn where
    toothAppend :: Tooth -> syn -> syn

teethAppend :: forall syn. ToothAppendable syn => UpPath -> syn -> syn
teethAppend Nil syn = syn
teethAppend (tooth : teeth) syn = teethAppend teeth (toothAppend tooth syn)

instance toothAppendableTerm :: ToothAppendable Term where
    toothAppend tooth term = hole

instance toothAppendableType :: ToothAppendable Type where
    toothAppend tooth ty = hole
