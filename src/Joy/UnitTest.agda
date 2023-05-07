{-# OPTIONS --allow-unsolved-metas #-}

module Joy.UnitTest where

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

module Addition where

  open Category addition

  usingAddition : 5 ∘ 3 ≡ 8
  usingAddition = refl
