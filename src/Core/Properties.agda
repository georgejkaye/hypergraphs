{-# OPTIONS --exact-split --safe #-}

open import Core.Hypergraph
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.List.Membership.Propositional
open import Data.Fin
open import Data.Fin.Patterns
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality

open Hypergraph

module Core.Properties where

data is-source-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) {p : inhab k l es} : V f → E f k l p → Set where
    iss : (v : V f) (e : E f k l p) → v ∈ sources f k l {p} e → is-source-of f k l v e

test : is-source-of example 1 2 {yes 1 2 ((1 , 2) ∷ (3 , 1) ∷ []) (here refl)} 1F 0F
test = iss 1F 0F (here refl)
