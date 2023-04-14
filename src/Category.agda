{-# OPTIONS --allow-unsolved-metas #-}

module Category where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Vec hiding (map)
import Data.Vec as V
open import Data.Product as P hiding (map)
open import Data.Fin.Base as F hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties hiding (bounded)
open import Relation.Binary.PropositionalEquality

-- A category
-- we need to make it Set1 to deal with the ominious size issue
-- data:
-- objects: things of type 'Set' are our obects
-- arrows: cat encodes arrows
record Category (cat : Set -> Set -> Set)  : Set1 where
  constructor category
  field
    -- structure
    identity : {a : Set} -> cat a a
    _∘_ : {a b c : Set} ->  cat b c -> cat a b -> cat a c

    -- properties
    unit_a : {a b : Set} (f : cat a b) -> f ∘ identity ≡ f
    unit_b : {a b : Set} (f : cat a b) -> identity ∘ f ≡ f

    associativity : {a b c d : Set} (f : cat a b) (g : cat b c) (h : cat c d) -> (h ∘ g) ∘ f ≡  h ∘ (g ∘ f)
