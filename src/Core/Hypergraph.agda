{-# OPTIONS --exact-split --safe #-}

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
s example {1} {2} 0F zero (s≤s z≤n) = 1F
s example {3} {1} 0F zero (s≤s z≤n) = 0F
s example {3} {1} 0F (suc zero) (s≤s (s≤s z≤n)) = 3F
s example {3} {1} 0F (suc (suc zero)) (s≤s (s≤s (s≤s z≤n))) = 0F
s example {suc (suc (suc (suc (suc (suc k)))))} {zero} () n p
s example {suc (suc (suc (suc (suc (suc k)))))} {suc zero} () n p
s example {suc (suc (suc (suc (suc (suc k)))))} {suc (suc zero)} () n p
s example {suc (suc (suc (suc (suc (suc k)))))} {suc (suc (suc l))} () n p
t example {1} {2} 0F 0 (s≤s z≤n) = 2F
t example {1} {2} 0F (suc zero) (s≤s (s≤s z≤n)) = 3F
t example {3} {1} 0F 0 (s≤s z≤n) = 1F
t example {suc (suc (suc (suc (suc k))))} {suc zero} () n p
t example {suc (suc (suc (suc zero)))} {suc (suc l)} () n p
t example {suc (suc (suc (suc (suc k))))} {suc (suc l)} () n p