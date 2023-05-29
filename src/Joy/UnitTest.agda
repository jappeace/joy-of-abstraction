{-# OPTIONS --allow-unsolved-metas #-}

module Joy.UnitTest where

open import Data.Nat.Properties as N
open import Data.Nat.Base
import Data.Integer.Base as Int
open import Data.Sign.Base as Sign using (Sign)
import Data.Integer.Base as Int
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
import Data.Integer.Base as Int
import Data.Integer.Properties as Int
import Agda.Primitive as Prim
open import Algebra.Core
import Relation.Binary.Core as BCore
open import Joy.Category
open import Joy.Homo
open ≡-Reasoning

module Addition where

  open Category addition

  usingAddition : 5 ∘ 3 ≡ 8
  usingAddition = refl


module MndTests where
  toInt : ℕ → Int.ℤ
  toInt xa = Int._⊖_ (N._*_ 2 xa) 0

  nxn : HomoMorphism addition addIntegers
  nxn = record {
        fun = toInt
        ; preserveStructure = λ {a = a} {b = b} →  begin
              toInt (Category._∘_ addition a b)
            ≡⟨⟩
              toInt (a + b)
            ≡⟨⟩
              Int._⊖_ (N._*_ 2 (a + b)) 0
            ≡⟨ cong (λ x → (Int._⊖_ x 0) ) N.*-distribˡ-+ ⟩
              Int._⊖_ (((N._*_ 2 a) + (N._*_ 2 b))) 0
            ≡⟨⟩
              Category._∘_ addIntegers (toInt a) (toInt b)
            ∎
      }

  open Category Mnd.mnd

  -- usingMnd = ∘
