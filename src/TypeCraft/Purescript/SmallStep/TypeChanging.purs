module TypeCraft.Purescript.SmallStep.TypeChanging where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.SmallStep.UTerm
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.Context

{-
PROBLEM:
This idea doesn't work because on Let we need to also do stuff to the type!
Not to mention that sometimes changes come UP FROM a constructor or something.
So this generic approach might work in DTT with a carefully generic view of things, but not here!

Here, it would REALLY need to be instead of Change, (Change + TyArgsChange + CtrParamsChange + .........)
-}

{-
downChange :: Label -> Change -> Array Change
downChange (LApp md {-Term-} {-Term-} Type Type) = ?h
downChange (LLambda md TermBind Type {-Term-} Type) = ?h
downChange (LVar md TermVarID (List TypeArg)) = ?h
downChange (LLet md TermBind (List TypeBind) {-Term-} Type {-Term-} Typ) = ?h
downChange (LData md TypeBind (List TypeBind) (List Constructor) {-Term-} Typ) = ?h
downChange (LTLet md TypeBind (List TypeBind) Type {-Term-} Type) = ?h
downChange (LTypeBoundary md Change {-Term-}) = ?h
downChange (LContextBoundary md TermVarID VarChange {-Term-}) = ?h
downChange (LHole md {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}) = ?h
downChange (LBuffer md {-Term-} Type {-Term-} Type) = ?h
-}