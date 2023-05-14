{-# OPTIONS --allow-unsolved-metas #-}

module Joy.Homo where

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
open import Joy.Category

open ≡-Reasoning

-- how does it know what HomoMorphism should be used with what monoid?
-- eg if I have a Monoid of addition over integers
-- and try to compose that with a monoid for union in sets,
-- how is that type safe with existentials?
-- how is the homomorpism constructed?


-- A homomorphism
-- TODO I think I temporaryly basterdised this by just making it work
-- on monids, I should relax the constraints later on for functors.
record HomoMorphism {l2 : Prim.Level} {A B : Set l2} (cat1 : Monoid A) (cat2 : Monoid B) : Set l2 where
  constructor homomorphism
  open Category cat1
  field
    -- structure
    fun : A -> B

    -- properties
    preserveStructure : { a b : A } -> fun (a ∘ b) ≡ (Category._∘_ cat2 (fun a) (fun b))
    identityEquality : fun identity ≡ Category.identity cat2

open HomoMorphism

identityHomo : {l2 : Prim.Level} {arrow : Set l2 } {cat : Monoid arrow } -> HomoMorphism cat cat
fun identityHomo a = a
preserveStructure identityHomo = refl
identityEquality identityHomo = refl

module Mnd where
  open Category

  mnd : {l2 : Prim.Level} -> ∀ (arrow : Set l2 ) -> Category {object  = Monoid arrow} HomoMorphism
  identity (mnd arrow) = identityHomo{arrow = arrow}


-- mnd : {l1 l2 : Prim.Level} {A B : Set l2}
--   {cat1 : Category {x = Unit.⊤} (λ _ _ → A)}
--   {cat2 : Category {x = Unit.⊤} (λ _ _ → B)} ->
--   (homo : HomoMorphism cat1 cat2)
--   -> Category {l1 =  l1 Prim.⊔ l2} {l2 = Prim.lsuc l2} {x = cat1} (λ a b -> cat2)
