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

record Hypergraph (es : EdgeDecs) : Set₁ where
    
    field
        v : ℕ
        e : ℕ → ℕ → ℕ

    V : Set
    V = Fin v

    E : (k : ℕ) → (l : ℕ) → inhab k l es → Set
    E k l p = Fin (e k l)

    field
        s : (k l : ℕ) {p : inhab k l es} → (E k l p) → (Fin k) → V
        t : (k l : ℕ) {p : inhab k l es} → (E k l p) → (Fin l) → V

    sources : (k l : ℕ) {p : inhab k l es} → E k l p → List V 
    sources k l {p} e = map (λ i → s k l {p} e i) (allFin k)

    targets : (k l : ℕ) {p : inhab k l es} → E k l p → List V 
    targets k l {p} e = map (λ j → t k l {p} e j) (allFin l)

open Hypergraph

example : Hypergraph ((1 , 2) ∷ (3 , 1) ∷ [])
v example = 4
e example 1 1 = 0
e example 1 2 = 1
e example 3 1 = 1
e example 0 l = 0
e example 1 0 = 0
e example 1 (suc (suc (suc l))) = 0
e example 2 l = 0
e example 3 0 = 0
e example 3 (suc (suc l)) = 0
e example 4 l = 0
e example (suc (suc (suc (suc (suc k))))) l = 0
s example 1 2 0F 0F = 1F
s example 3 1 0F 0F = 0F
s example 3 1 0F 1F = 3F
s example 3 1 0F 2F = 0F
s example (suc (suc (suc (suc (suc (suc k)))))) 0 () n
s example (suc (suc (suc (suc (suc (suc k)))))) 1 () n
s example (suc (suc (suc (suc (suc (suc k)))))) 2 () n
s example (suc (suc (suc (suc (suc (suc k)))))) (suc (suc (suc l))) () n
t example 1 2 0F 0F = 2F
t example 1 2 0F 1F = 3F
t example 3 1 0F 0F = 1F
t example (suc (suc (suc (suc (suc k))))) (suc zero) () n
t example (suc (suc (suc (suc zero)))) (suc (suc l)) () n
t example (suc (suc (suc (suc (suc k))))) (suc (suc l)) () n