{-# OPTIONS --exact-split --safe #-}

open import Core.Hypergraph

open import Data.Nat
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns
open import Data.Product

open import Function.Definitions

open import Relation.Binary.PropositionalEquality

module Core.Morphism where

open Hypergraph

record _⇒_ {e1 e2 : EdgeDecs} (f : Hypergraph e1) (g : Hypergraph e2) : Set where
    field 
        vmap : V f → V g
        emap : (k l : ℕ) (p1 : inhab k l e1) (p2 : inhab k l e2) → E f k l p1 → E g k l p2
        sources-pres : (k l : ℕ) → (p1 : inhab k l e1) (p2 : inhab k l e2) (n : Fin k) → (e : E f k l p1) → vmap (s f k l {p1} e n) ≡ (s g k l {p2} (emap k l p1 p2 e) n)
        targets-pres : (k l : ℕ) → (p1 : inhab k l e1) (p2 : inhab k l e2) (n : Fin l) → (e : E f k l p1) → vmap (t f k l {p1} e n) ≡ (t g k l {p2} (emap k l p1 p2 e) n)
open _⇒_


data _≅_ {e1 e2 : EdgeDecs} (F : Hypergraph e1) (G : Hypergraph e2) : Set where
    equiv : ∀ k l → (f : F ⇒ G) → Bijective {!   !} {!   !} (vmap f) → Bijective {!   !} {!   !} (emap f k l) → F ≅ G

open _⇒_