{-# OPTIONS --type-in-type #-}

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.String

module Terms2 where

-- parametrized by a set of grammatical Sorts

module Grammar (Sort : Set) where
  record Construct : Set where
    field
      sort : Sort
      children : List Sort
      metadata : Set

  Language : Set
  Language = Construct → Set

  module Syntax (L : Language) where
    mutual
      data Exp : Sort → Set where
        term : {c : Construct}
          → L c
          → Construct.metadata c
          → subTerms (Construct.children c)
          → Exp (Construct.sort c)

      subTerms : List Sort → Set
      subTerms [] = ⊤
      subTerms (s ∷ l) = Exp s × (subTerms l)

      data ToothChildren : List Sort → Sort → Set → Set where
        here : ∀{s ss} → ToothChildren (s ∷ ss) s (subTerms ss)
        next : ∀{s ss innerSort subTerms} → ToothChildren ss innerSort subTerms
          → ToothChildren (s ∷ ss) innerSort (Exp s × subTerms)

      data Tooth : Sort → Sort → Set where
        tooth : {c : Construct}
          → L c
          → Construct.metadata c
          → ∀{innerSort subTerms}
          → ToothChildren (Construct.children c) innerSort subTerms
          → subTerms
          → Tooth (Construct.sort c) innerSort

-- Now, use this to define a simple Lang:
-- For now, it will be untyped, but well grammared.
-- Hopefully, I can figure out how to make it keep track of types and contexts.

open Grammar
open Grammar.Syntax

data Type : Set where
  Arrow : Type → Type → Type
  Base : Type

data Sort : Set where
  -- Extremely trivial typing (doesn't even keep track of context) just for demonstration purposes:
  STerm : Type → Sort
  SType : Sort

data Lang : Construct Sort → Set where
  lambda : (A : Type) → {B : Type}
    → Lang record { sort = STerm (Arrow A B) ; children = (STerm B) ∷ [] ; metadata = String}
  var : (T : Type) → Lang record { sort = STerm T ; children = [] ; metadata = String}
  lett : ∀{A B}
    → Lang record { sort = STerm B ; children = STerm A ∷ SType ∷ STerm B ∷ [] ; metadata = String}
  arrow : Lang record {sort = SType ; children = SType ∷ SType ∷ [] ; metadata = ⊤}
  unit : Lang record {sort = SType ; children = [] ; metadata = ⊤}


LangTerm : Type → Set
LangTerm T = Exp Sort Lang (STerm T)

LangType : Set
LangType = Exp Sort Lang SType

LangTooth : Sort → Sort → Set
LangTooth = Tooth Sort Lang

-- An example program:
{-
let x = lambda y . y : unit → unit in
x
-}

exampleProg : LangTerm (Arrow Base Base)
exampleProg = term lett "x"
  (term (lambda Base) "y" (term (var Base) "y" tt , tt)
  , term arrow tt
    (term unit tt tt
    , term unit tt tt , tt)
  , term (var _) "x" tt , tt )


-- An example tooth:
{-
let x = lambda y . y : [hole] in
x
-}
exampleTooth : LangTooth (STerm (Arrow Base Base)) SType
exampleTooth = tooth lett "x"
  (next here)
  (term (lambda Base) "y" ((term (var Base) "y" tt , tt))
  , term (var _) "x" tt , tt)
