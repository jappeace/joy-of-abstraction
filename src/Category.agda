{-# OPTIONS --allow-unsolved-metas #-}

module Category where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Data.Product as P hiding (map)
open import Data.Fin.Base as F hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties hiding (bounded)
open import Relation.Binary.PropositionalEquality
import Data.Nat.Base as N
open import Data.Nat.Base
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


-- A category
-- we need to make it Set1 to deal with the ominious size issue
-- data:
-- objects: things of type 'Set' are our obects
-- arrows: cat encodes arrows
record Category {x : Set} (cat : x -> x -> Set)  : Set1 where
  constructor category
  field
    -- structure
    identity : {a : x} -> cat a a
    _∘_ : {a b c : x} ->  cat b c -> cat a b -> cat a c

    -- properties
    unit₁ : {a b : x} (f : cat a b) -> f ∘ identity ≡ f
    unit₂ : {a b : x} (f : cat a b) -> identity ∘ f ≡ f

    associativity : {a b c d : x} (f : cat a b) (g : cat b c) (h : cat c d) -> (h ∘ g) ∘ f ≡  h ∘ (g ∘ f)


leq-refl : (n : N.ℕ) -> n N.≤ n
leq-refl N.zero = N.z≤n
leq-refl (N.suc n) = N.s≤s (leq-refl n)

leq-zero' : (n : ℕ) -> (n ≤ zero) → (zero ≤ zero)
leq-zero' zero _ = z≤n
leq-zero' (suc _) ()

leq-zero : (n : N.ℕ) -> (n ≤ zero) ≡ (zero ≤ zero)
leq-zero zero = refl
leq-zero (suc n) =
  begin
    n ≤ zero
  ≡⟨ leq-zero' n (N.s≤s n) ⟩
    zero ≤ zero
  ∎




leq-trans : (a b c : N.ℕ) -> (b ≤ c) -> (a ≤ b) -> (a ≤ c)
leq-trans zero b c bc ab = z≤n
leq-trans a zero c bc ab = leq-zero' a bc

open Category

leq : Category (N._≤_)
identity leq {n} = leq-refl n
leq ab ∘ bc = leq-trans ab bc
