{-# OPTIONS --exact-split --safe #-}

open import Data.Nat
open import Data.Fin hiding (_<_ ; _≤_)
open import Data.Fin.Patterns
open import Data.List
open import Data.List.Relation.Unary.Any using (Any ; here ; there)
open import Data.Product hiding (map)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All.Properties using (all-upTo)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (id)

module Core.Hypergraph where

data inhab : ℕ → ℕ → (List (ℕ × ℕ)) → Set where
    yes : ∀ k l p → (k , l) ∈ p → inhab k l p

EdgeDecs : Set
EdgeDecs = List (ℕ × ℕ)

record Hypergraph : Set₁ where

    field
        ed : EdgeDecs
        v : ℕ
        e : ℕ → ℕ → ℕ

    V : Set
    V = Fin v

    E : (k : ℕ) → (l : ℕ) → inhab k l ed → Set
    E k l p = Fin (e k l)

    field
        s : (k l : ℕ) {p : inhab k l ed} → (E k l p) → (Fin k) → V
        t : (k l : ℕ) {p : inhab k l ed} → (E k l p) → (Fin l) → V

    sources : (k l : ℕ) (p : inhab k l ed) → E k l p → List V 
    sources k l p e = map (λ i → s k l {p} e i) (allFin k)

    targets : (k l : ℕ) (p : inhab k l ed) → E k l p → List V 
    targets k l p e = map (λ j → t k l {p} e j) (allFin l)

open Hypergraph