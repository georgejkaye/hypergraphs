{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Fin hiding (_<_)
open import Data.Fin.Patterns

module Core.Hypergraph where

record Hypergraph : Set₁ where
    
    field
        v : ℕ
        e : ℕ → ℕ → ℕ

    V : Set
    V = Fin v

    E : ℕ → ℕ → Set
    E k l = Fin (e k l)

    field
        s : {k l : ℕ} → (E k l) → (n : ℕ) → n < k → V
        t : {k l : ℕ} → (E k l) → (n : ℕ) → n < l → V


open Hypergraph

example : Hypergraph 
v example = 4
e example 3 1 = 1
e example 1 2 = 1
e example k l = 0
s example {3} {1} 0F zero p = 0F
s example {3} {1} 0F (suc zero) p = 1F
s example {3} {1} 0F (suc (suc zero)) (s≤s (s≤s (s≤s z≤n))) = 0F
s example {1} {2} 0F zero (s≤s z≤n) = 2F
s example {3} {1} 0F (suc n) p = {!   !}
s example {1} {2} x n p = {!   !}
t example = {!   !}