{-# OPTIONS --allow-unsolved-metas #-}

module Category where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
import Data.Nat.Base as N
open import Data.Nat.Base

open ≡-Reasoning


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

leq-trans : {a b c : ℕ} -> (b ≤ c) -> (a ≤ b) -> (a ≤ c)
leq-trans  bc z≤n = z≤n
leq-trans  (N.s≤s bc) (N.s≤s ab) = N.s≤s (leq-trans bc ab)

leq-left : {a b : ℕ} -> ( f : a ≤ b ) -> (leq-trans f (leq-refl a)) ≡ f
leq-left z≤n = refl
leq-left { a = suc a } { b = b } (N.s≤s bc) =
  begin
     (leq-trans (N.s≤s bc) (leq-refl (suc a)))
  ≡⟨ cong (λ x → leq-trans (N.s≤s bc) x) refl ⟩
     (leq-trans (N.s≤s bc) ((suc a) ≤ (suc a) ))
  ≡⟨⟩
    N.s≤s bc
  ∎

open Category

leq : Category (N._≤_)
identity leq {n} = leq-refl n
_∘_ leq bc ab = leq-trans bc ab
unit₁ leq f =
  begin
    f ∘ identity
  ≡⟨⟩
    f
  ∎
