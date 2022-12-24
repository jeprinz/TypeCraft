module TypeCraft.Purescript.Dentist where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Util (hole)

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