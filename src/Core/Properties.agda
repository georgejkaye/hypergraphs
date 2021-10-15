{-# OPTIONS --exact-split --safe #-}

open import Data.Nat
open import Data.Fin
open import Data.Fin.Patterns

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any

open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Helpers.Lists

open import Core.Hypergraph

open Hypergraph    

module Core.Properties where

data is-source-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    iss : (v : V f) (e : E f k l p) → v in-list sources f k l p e → is-source-of f k l p v e

data is-not-source-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    iss : (v : V f) (e : E f k l p) → v not-in-list sources f k l p e → is-not-source-of f k l p v e

data is-target-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    ist : (v : V f) (e : E f k l p) → v in-list targets f k l p e → is-target-of f k l p v e

data is-not-target-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    ist : (v : V f) (e : E f k l p) → v not-in-list targets f k l p e → is-not-target-of f k l p v e

data v-left-monogamous {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → Set where 
    none : (v : V f) → ∀ e → is-not-target-of f k l p v e → v-left-monogamous f k l p v
    one  : (v : V f) → ∃ (λ e → is-target-of f k l p v e × ((e1 : E f k l p) → e ≢ e1 → is-not-target-of f k l p v e1)) → v-left-monogamous f k l p v

data v-right-monogamous {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → Set where 
    none : (v : V f) → ∀ e → is-not-source-of f k l p v e → v-right-monogamous f k l p v
    one  : (v : V f) → ∃ (λ e → is-source-of f k l p v e × ((e1 : E f k l p) → e ≢ e1 → is-not-source-of f k l p v e1)) → v-right-monogamous f k l p v

data left-monogamous {es : EdgeDecs} : Hypergraph es → Set where
    lm : (f : Hypergraph es) → (v : V f) → ∀ k l → (p : inhab k l es) → v-left-monogamous f k l p v → left-monogamous f

data right-monogamous {es : EdgeDecs} : Hypergraph es → Set where
    rm : (f : Hypergraph es) → (v : V f) → ∀ k l → (p : inhab k l es) → v-right-monogamous f k l p v → right-monogamous f

data monogamous {es : EdgeDecs} (f : Hypergraph es) : Set where
    mon : left-monogamous f × right-monogamous f → monogamous f