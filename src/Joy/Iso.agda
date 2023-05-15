{-# OPTIONS --allow-unsolved-metas #-}

module Joy.Iso where

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

-- TODO I'm not sure if this is right,
-- I just want be able t odefine this for a single arrow of a category
-- an arrow that can be inverted and result in identities
record IsoMorphism {l1 l2 : Prim.Level } {object : Set l1} (arrow : object -> object -> Set l2 ) {isCategory : Category arrow} : Set (l1 Prim.⊔ l2) where
  constructor iso
  open Category isCategory public
  field
    inverse : {a b : object} -> arrow a b -> arrow b a

    anhilationʳ : {a b : object} (f : arrow a b) -> f ∘ inverse f  ≡ identity { a = b }
    anhilationˡ : {a b : object} (f : arrow a b) -> inverse f ∘ f ≡ identity { a = a }
