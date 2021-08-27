{-# OPTIONS --exact-split --safe #-}

open import Core.Hypergraph

open import Data.Nat
open import Data.Fin using () renaming (suc to fsuc)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality

module Core.Morphism where

open Hypergraph

record _⇒_ (f g : Hypergraph) : Set where
    field 
        vmap : V f → V g
        emap : {k l : ℕ} → E f k l → E g k l
        sources-pres : {k l : ℕ} → (n : ℕ) → (p : n < k) → (e : E f k l) → vmap (s f e n p) ≡ (s g (emap e) n p)
        targets-pres : {k l : ℕ} → (n : ℕ) → (p : n < l) → (e : E f k l) → vmap (t f e n p) ≡ (t g (emap e) n p)

open _⇒_