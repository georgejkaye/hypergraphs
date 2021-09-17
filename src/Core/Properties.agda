{-# OPTIONS --exact-split --safe #-}

open import Core.Hypergraph
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.List.Membership.Propositional
open import Data.Fin
open import Data.Fin.Patterns
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open Hypergraph    

module Core.Properties where

data _in-list_ {A : Set} : A → List A → Set where
    in-head : ∀ a xs → a in-list (a ∷ xs) 
    in-cons : ∀ a x xs → a in-list xs → a in-list (x ∷ xs)

data _not-in-list_ {A : Set} : A → List A → Set where
    not-in-empty : ∀ a → a not-in-list []
    not-in-cons  : ∀ a x xs → a ≢ x → a not-in-list xs → a not-in-list (x ∷ xs) 

data is-source-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    iss : (v : V f) (e : E f k l p) → v in-list sources f k l p e → is-source-of f k l p v e

data is-not-source-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    iss : (v : V f) (e : E f k l p) → v not-in-list sources f k l p e → is-not-source-of f k l p v e

data is-target-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    ist : (v : V f) (e : E f k l p) → v in-list targets f k l p e → is-target-of f k l p v e

data is-not-target-of {es : EdgeDecs} (f : Hypergraph es) (k l : ℕ) (p : inhab k l es) : V f → E f k l p → Set where
    ist : (v : V f) (e : E f k l p) → v not-in-list targets f k l p e → is-not-target-of f k l p v e


data left-monogamous {es : EdgeDecs} (f : Hypergraph es) : V f → Set where
    lm : (v : V f) → (∃ (λ k → ∃ λ l → (p : inhab k l es) → ∃ (λ e → is-target-of f k l p v e × (∀ e1 → e ≢ e1 → is-not-target-of f k l p v e1)))) ⊎ (∀ k l p e → is-not-target-of f k l p v e) →  left-monogamous f v

data right-monogamous {es : EdgeDecs} (f : Hypergraph es) : V f → Set where
    rm : (v : V f) → (∃ (λ k → ∃ λ l → (p : inhab k l es) → ∃ (λ e → is-source-of f k l p v e × (∀ e1 → e ≢ e1 → is-not-source-of f k l p v e1))))⊎ (∀ k l p e → is-not-target-of f k l p v e) → right-monogamous f v

record monogamous {es : EdgeDecs} (f : Hypergraph es) : Set where
    field
        left : (v : V f) → left-monogamous f v
        right : (v : V f) → right-monogamous f v