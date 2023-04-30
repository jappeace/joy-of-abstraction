{-# OPTIONS --allow-unsolved-metas #-}

module Joy.Category where

open import Data.Product
import Algebra.Structures as Struct
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality.Core as EqCore
import Data.Nat.Base as N
import Data.Nat.Properties as P
import Agda.Builtin.Unit as Unit
open import Data.Nat.Base
import Data.Integer.Base as Int
import Data.Integer.Properties as Int
import Agda.Primitive as Prim
open import Algebra.Core
import Relation.Binary.Core as BCore

open ≡-Reasoning

-- A category
-- we need to make it Set1 to deal with the ominious size issue
-- data:
-- objects: things of type 'Set' are our obects
-- arrows: cat encodes arrows
record Category {l1 l2 : Prim.Level } {x : Set l1} (cat : x -> x -> Set l2)  : Set (l1 Prim.⊔ l2) where
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


-- example of an equivelance relation
leq : Category (N._≤_)
identity leq {n} = leq-refl n
_∘_ leq bc ab = leq-trans bc ab
unitʳ leq f = leq-prop _ _
unitˡ leq f = leq-prop _ _
associativity leq f g h = leq-prop _ _

-- another example (needed for inverses
-- here we set x to something, but it should be able to do for anything
eq : (x : Set) → Category { x = x } (_≡_)
identity (eq _) {n} = refl
_∘_ (eq _) ab bc = EqCore.trans bc ab
unitʳ (eq _) f = refl
unitˡ (eq _) refl = refl
associativity (eq _) refl g h = refl


-- example of a monoid
-- we need to assign x = Unit.⊤ because that particular type asserts
-- there is only ONE object.
-- any good ol' type on `x` would typecheck since it's used,
-- but that not be right.
addition : Category {x = Unit.⊤ } (λ _ _ → ℕ) -- the arrows are the numbers, so we need to neglect the type args
identity addition = zero
_∘_ addition bc ab = bc + ab
unitˡ addition a = P.+-identityˡ a
unitʳ addition a = P.+-identityʳ a
associativity addition a b c = P.+-assoc c b a

-- same ol trick for integers, so this is also a monoid over addition
addIntegers : Category {x = Unit.⊤ } (λ a b → Int.ℤ) -- the arrows are the numbers, so we need to neglect the type args
identity addIntegers = Int.0ℤ
_∘_ addIntegers bc ab = Int._+_ bc ab
unitˡ addIntegers a = Int.+-identityˡ a
unitʳ addIntegers a = Int.+-identityʳ a
associativity addIntegers a b c = Int.+-assoc c b a


-- the so called motivating example for category theory
-- • objects: all sets
-- • morphisms: a morphism A B is a function A B
-- • identities: given a set A, the identity is the identity function 1A
-- • composition: composition of morphisms is composition of functions.
--
setsAndFunctions : {l : Prim.Level } -> Category { l2 = l } (λ a b -> (a -> b))
identity setsAndFunctions {arg} = λ a -> a
_∘_ setsAndFunctions bc ab = λ a → bc (ab a)
-- the proofs are enforced by agda's typesystem.
unitˡ setsAndFunctions a = refl
unitʳ setsAndFunctions a = refl
associativity setsAndFunctions a b c = refl

-- If you're a monoid, you're a category
monoidIsCategory : {a : Prim.Level } {A : Set a} {∙ : Op₂ A} {ε : A} ->
                  (Struct.IsMonoid (_≡_) ∙ ε) → Category {x = Unit.⊤ } (λ _ _ → A)
identity (monoidIsCategory {ε = ε} m) = ε
_∘_ (monoidIsCategory {∙ = ∙} m) bc ab = ∙ bc ab
unitˡ (monoidIsCategory m) cat = (Struct.IsMonoid.identityˡ m) cat
unitʳ (monoidIsCategory m) cat = Struct.IsMonoid.identityʳ m cat
associativity (monoidIsCategory m) f g h = Struct.IsSemigroup.assoc (Struct.IsMonoid.isSemigroup m) h g f


-- we can now get re-usable categories:
addIntegersBigly : Category {x = Unit.⊤ } (λ a b → Int.ℤ) -- the arrows are the numbers, so we need to neglect the type args
addIntegersBigly = monoidIsCategory  Int.+-0-isMonoid
