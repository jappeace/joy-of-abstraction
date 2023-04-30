{-# OPTIONS --allow-unsolved-metas #-}

module Category where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
import Data.Nat.Base as N
import Data.Nat.Properties as P
import Agda.Builtin.Unit as Unit
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
    unitʳ : {a b : x} (f : cat a b) -> f ∘ identity ≡ f
    unitˡ : {a b : x} (f : cat a b) -> identity ∘ f ≡ f

    associativity : {a b c d : x} (f : cat a b) (g : cat b c) (h : cat c d) -> (h ∘ g) ∘ f ≡  h ∘ (g ∘ f)


leq-refl : (n : N.ℕ) -> n N.≤ n
leq-refl N.zero = N.z≤n
leq-refl (N.suc n) = N.s≤s (leq-refl n)

leq-trans : {a b c : ℕ} -> (b ≤ c) -> (a ≤ b) -> (a ≤ c)
leq-trans  bc z≤n = z≤n
leq-trans  (N.s≤s bc) (N.s≤s ab) = N.s≤s (leq-trans bc ab)

leq-prop : {a b : ℕ} (x y : a ≤ b) → x ≡ y
leq-prop z≤n z≤n = refl
leq-prop (s≤s x) (s≤s y) = cong s≤s (leq-prop x y)

open Category

record InvCategory {x : Set} {cat : x -> x -> Set } (base : Category { x = x } cat) : Set1 where
  constructor invcategory
  field
    inverse : {a b : x} -> cat a b -> cat b a

    anhilationʳ : {a b : x} (f : cat a b) -> f ∘ inverse f  ≡ identity
    anhilationˡ : {a b : x} (f : cat a b) -> inverse f ∘ f ≡ identity


-- example of an equivelance relation
leq : Category (N._≤_)
identity leq {n} = leq-refl n
_∘_ leq bc ab = leq-trans bc ab
unitʳ leq f = leq-prop _ _
unitˡ leq f = leq-prop _ _
associativity leq f g h = leq-prop _ _

-- example of a monoid
-- we need to assign x = Unit.⊤ because that particular type asserts
-- there is only ONE object.
-- any good ol' type on `x` would typecheck since it's used,
-- but that not be right.
addition : Category {x = Unit.⊤ } (λ a b → ℕ) -- the arrows are the numbers, so we need to neglect the type args
identity addition = zero
_∘_ addition bc ab = bc + ab
unitˡ addition a = P.+-identityˡ a
unitʳ addition a = P.+-identityʳ a
associativity addition a b c = P.+-assoc c b a
