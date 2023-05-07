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


-- A homomorphism
record HomoMorphism {l2 : Prim.Level} {A B : Set l2} (cat1 : Category {x = Unit.⊤} (λ _ _ → A)) (cat2 : Category {x = Unit.⊤} (λ _ _ → B)) : Set l2 where
  constructor homomorphism
  field
    -- structure
    fun : A -> B

    -- properties
    preserveStructure : { a b : A } -> fun (_∘_ cat1 a b) ≡ (_∘_ cat2 (fun a) (fun b))
    identityEquality : fun (identity cat1) ≡ identity cat2

mnd : {l1 l2 : Prim.Level} {A B : Set l2}
  {cat1 : Category {x = Unit.⊤} (λ _ _ → A)}
  {cat2 : Category {x = Unit.⊤} (λ _ _ → B)} ->
  (homo : HomoMorphism cat1 cat2)
  -> Category {l1 =  l1 Prim.⊔ l2} {l2 = Prim.lsuc l2} {x = cat1} (λ a b -> cat2)
