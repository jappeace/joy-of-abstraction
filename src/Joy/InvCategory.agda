{-# OPTIONS --allow-unsolved-metas #-}

module Joy.InvCategory where

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
-- this allows encoding of groups for example.
-- I think this means our category has a dual? I'm not sure
record InvCategory {l1 l2 : Prim.Level } {x : Set l1} (cat : x -> x -> Set l2 ) : Set (l1 Prim.⊔ l2) where
  constructor invCategory
  field
    isCategory : Category cat
  open Category isCategory public
  field
    inverse : {a b : x} -> cat a b -> cat b a

    anhilationʳ : {a b : x} (f : cat a b) -> f ∘ inverse f  ≡ identity
    anhilationˡ : {a b : x} (f : cat a b) -> inverse f ∘ f ≡ identity

open InvCategory

-- makes a group out of the addition monoid
-- additionGroup : InvCategory {x = Unit.⊤ } (λ a b → ℕ)
-- isCategory additionGroup = addition
-- inverse additionGroup a = 0 - a -- bitch, don't work, you can't define this on just naturals

additionGroup : InvCategory {x = Unit.⊤ } (λ _ _ → ℤ)
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
eqInv : (x : Set) → InvCategory { x = x } (_≡_)
isCategory (eqInv x) = eq x
inverse (eqInv x) relation = sym relation
anhilationʳ (eqInv x) refl = refl
anhilationˡ (eqInv x) refl = refl

-- A group is an inverse category
groupIsInvCategory : {a : Prim.Level } {A : Set a} {∙ : Op₂ A} {ε : A} {_⁻¹ : Op₁ A} ->
                  (Struct.IsGroup (_≡_) ∙ ε _⁻¹) → InvCategory {x = Unit.⊤ } (λ _ _ → A)
isCategory (groupIsInvCategory m) = monoidIsCategory (Struct.IsGroup.isMonoid m)
inverse (groupIsInvCategory {_⁻¹ = _⁻¹} m) relation = relation ⁻¹
anhilationʳ (groupIsInvCategory m) r = Struct.IsGroup.inverseʳ m r
anhilationˡ (groupIsInvCategory m) l = Struct.IsGroup.inverseˡ m l


addIntegersBiglyGroup : InvCategory (λ _ _ → ℤ)
addIntegersBiglyGroup = groupIsInvCategory Int.+-0-isGroup
