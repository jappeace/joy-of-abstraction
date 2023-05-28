{-# OPTIONS --allow-unsolved-metas #-}

module Joy.Iso where

import Algebra.Structures as Struct
open import Algebra.Core
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
import Agda.Builtin.Unit as Unit
open import Joy.Category
open import Data.Integer.Base
import Data.Integer.Properties as Int
import Agda.Primitive as Prim

open ≡-Reasoning

-- this is a categorical version of injectivity
--
-- A function f : A B is called injective if
-- ∀x, y ∈ A, f (x) = f (y) ⇒ x = y.
--
-- A morphism f = a → b in a category C is called a monomor-
-- phism or monic if, given any fork diagram as above in C,
--  f . s = f . t => s = t
record Monomorphism {l1 l2 : Prim.Level } {object : Set l1} (arrow : object -> object -> Set l2 ) {isCategory : Category arrow} : Set (l1 Prim.⊔ l2) where
  constructor monic
  open Category isCategory public
    field
      isMonic : { a b m : object } { f : arrow a b } { s t : arrow m a } -> f ∘ s ≡ f ∘ t -> s ≡ t



-- A function f : A B is called surjective if
-- ∀b ∈ B ∃ a ∈ A such that f (a) = b
--

-- TODO I'm not sure if this is right,
-- I just want be able t odefine this for a single arrow of a category
-- an arrow that can be inverted and result in identities
record IsoMorphism {l1 l2 : Prim.Level } {object : Set l1} (arrow : object -> object -> Set l2 ) {isCategory : Category arrow} : Set (l1 Prim.⊔ l2) where
  constructor iso
  open Category isCategory public
  field
    inverse : {a b : object} -> arrow a b -> arrow b a

    anhilationʳ : {a b : object} (f : arrow a b) -> f ∘ inverse f  ≡ identity { a = b }
    anhilationˡ : {a b : object} (f : arrow a b) -> inverse f ∘ f ≡ identity { a = a }


-- T 14.10 Can you prove that a function is an isomorphism of sets if and only if it is a bijection?
-- I guess two thigns are asked,
-- 1. if you're an isomorpism, then you're a bijection
-- 2. if you're an bijection, then you're an isomorphism.
