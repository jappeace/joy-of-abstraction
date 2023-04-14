{-# OPTIONS --allow-unsolved-metas #-}

module Mul where

open import Function.Base
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

record Category (cat : Set -> Set -> Set)  : Set where
  constructor category
  field
    identity : {a : Set} -> cat a a
    compose : {a b c : Set} ->  cat b c -> cat a b -> cat a c
    unit_a : {a b : Set} (f : cat a b) -> compose f identity ≡ f
    unit_b : {a b : Set} (f : cat a b) -> compose identity f ≡ f

    associativity : {a b c d : Set} (f : cat a b) (g : cat b c) (h : cat c d) ->  compose (compose h g) f ≡ compose h (compose g f)
