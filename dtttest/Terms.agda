{-# OPTIONS --type-in-type #-}

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.String

module Terms where

-- parametrized by a set of grammatical Sorts

data _∈_ {X : Set} : X → List X → Set where
  here : ∀{x l} → x ∈ (x ∷ l)
  next : ∀{x y l} → x ∈ l → x ∈ (y ∷ l)

module Grammar (Sort : Set) where
  record Construct : Set where
    field
      sort : Sort
      children : List Sort
      metadata : Set

  Language : Set
  Language = List Construct

  module Syntax (L : Language) where
    mutual
      data Exp : Sort → Set where
        term : (c : Construct)
          → c ∈ L
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
        tooth : (c : Construct)
          → c ∈ L
          → Construct.metadata c
          → ∀{innerSort subTerms}
          → ToothChildren (Construct.children c) innerSort subTerms
          → subTerms
          → Tooth (Construct.sort c) innerSort

-- Now, use this to define a simple STLC:
-- For now, it will be untyped, but well grammared.
-- Hopefully, I can figure out how to make it keep track of types and contexts.

open Grammar
open Grammar.Syntax

data Sort : Set where
  Term : Sort
  Type : Sort

lambda : Construct Sort
lambda = record { sort = Term ; children = Term ∷ [] ; metadata = String}

var : Construct Sort
var = record { sort = Term ; children = [] ; metadata = String}

lett : Construct Sort
lett = record { sort = Term ; children = Term ∷ Type ∷ Term ∷ [] ; metadata = String}

arrow : Construct Sort
arrow = record {sort = Type ; children = Type ∷ Type ∷ [] ; metadata = ⊤}

unit : Construct Sort
unit = record {sort = Type ; children = [] ; metadata = ⊤}

STLC : Language Sort
STLC = lambda ∷ var ∷ lett ∷ arrow ∷ unit ∷ []

STLCTerm : Set
STLCTerm = Exp Sort STLC Term

STLCType : Set
STLCType = Exp Sort STLC Type

STLCTooth : Sort → Sort → Set
STLCTooth = Tooth Sort STLC

-- An example program:
{-
let x = lambda y . y : unit → unit in
x
-}

exampleProg : STLCTerm
exampleProg = term lett (next (next here)) "x"
  (term lambda here "y" (term var (next here) "y" tt , tt)
  , term arrow (next (next (next here))) tt
    (term unit (next (next (next (next here)))) tt tt
    , term unit (next (next (next (next here)))) tt tt , tt)
  , term var (next here) "x" tt , tt )


-- An example tooth:
{-
let x = lambda y . y : [hole] in
x
-}
exampleTooth : STLCTooth Term Type
exampleTooth = tooth lett (next (next here))
  "x" (next here)
  (term lambda here "y" ((term var (next here) "y" tt , tt))
  , term var (next here) "x" tt , tt)
