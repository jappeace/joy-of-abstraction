{-# OPTIONS --allow-unsolved-metas #-}

module Joy.InvCategory where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Vec hiding (map)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
import Agda.Builtin.Unit as Unit
open import Joy.Category
open import Data.Integer.Base
import Data.Integer.Properties as Int

open ≡-Reasoning

-- this is an extension of a category with invertable arrows.
-- this allows encoding of groups for example.
record InvCategory {x : Set} (cat : x -> x -> Set ) : Set1 where
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

additionGroup : InvCategory {x = Unit.⊤ } (λ a b → ℤ)
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
