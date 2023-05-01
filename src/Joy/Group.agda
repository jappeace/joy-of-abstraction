{-# OPTIONS --allow-unsolved-metas #-}

module Joy.Group where

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

-- this is an extension of a category with invertable arrows.
-- It's a groupoid and not a group because this record put no restriction
-- on the count of objects, the individual definitions have to make it a Group by
-- Groupoid {x = Unit.⊤ }
record Groupoid {l1 l2 : Prim.Level } {x : Set l1} (cat : x -> x -> Set l2 ) : Set (l1 Prim.⊔ l2) where
  constructor invCategory
  field
    isCategory : Category cat
  open Category isCategory public
  field
    inverse : {a b : x} -> cat a b -> cat b a

    anhilationʳ : {a b : x} (f : cat a b) -> f ∘ inverse f  ≡ identity
    anhilationˡ : {a b : x} (f : cat a b) -> inverse f ∘ f ≡ identity

open Groupoid

-- makes a group out of the addition monoid
-- additionGroup : Groupoid {x = Unit.⊤ } (λ a b → ℕ)
-- isCategory additionGroup = addition
-- inverse additionGroup a = 0 - a -- bitch, don't work, you can't define this on just naturals

additionGroup : Groupoid {x = Unit.⊤ } (λ _ _ → ℤ)
isCategory additionGroup = addIntegers
inverse additionGroup a = - a
anhilationʳ additionGroup n = Int.m≡n⇒m-n≡0 n n refl
anhilationˡ additionGroup n = begin
  (- n) + n
  ≡⟨ Int.+-comm (- n) n ⟩
  n + (- n)
  ≡⟨ Int.m≡n⇒m-n≡0 n n refl ⟩
   0ℤ
  ∎


-- this seems rather trivial but I wanted two examples of an
-- invertable catagory.
eqInv : (x : Set) → Groupoid { x = x } (_≡_)
isCategory (eqInv x) = eq x
inverse (eqInv x) relation = sym relation
anhilationʳ (eqInv x) refl = refl
anhilationˡ (eqInv x) refl = refl

-- A group is an inverse category
groupIsGroupoid : {a : Prim.Level } {A : Set a} {∙ : Op₂ A} {ε : A} {_⁻¹ : Op₁ A} ->
                  (Struct.IsGroup (_≡_) ∙ ε _⁻¹) → Groupoid {x = Unit.⊤ } (λ _ _ → A)
isCategory (groupIsGroupoid m) = monoidIsCategory (Struct.IsGroup.isMonoid m)
inverse (groupIsGroupoid {_⁻¹ = _⁻¹} m) relation = relation ⁻¹
anhilationʳ (groupIsGroupoid m) r = Struct.IsGroup.inverseʳ m r
anhilationˡ (groupIsGroupoid m) l = Struct.IsGroup.inverseˡ m l


addIntegersBiglyGroup : Groupoid (λ _ _ → ℤ)
addIntegersBiglyGroup = groupIsGroupoid Int.+-0-isGroup
