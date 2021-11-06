{-# OPTIONS --exact-split --safe #-}

open import Core.Hypergraph

open import Data.Nat
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns
open import Data.Product

open import Function.Definitions using (Bijective ; Injective)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Level renaming (zero to lzero ; suc to lsucc)
open import Categories.Category.Core

module Core.Morphism where

open Hypergraph

record _⇒_ (F : Hypergraph) (G : Hypergraph) : Set where
    src : Hypergraph
    src = F
    trg : Hypergraph
    trg = G
    field 
        vmap : V F → V G
        emap : (k l : ℕ) (p1 : inhab k l (ed F)) (p2 : inhab k l (ed G)) → E F k l p1 → E G k l p2
        sources-pred : (k l : ℕ) → (p1 : inhab k l (ed F)) (p2 : inhab k l (ed G)) (n : Fin k) → (e : E F k l p1) → vmap (s F k l {p1} e n) ≡ (s G k l {p2} (emap k l p1 p2 e) n)
        targets-pred : (k l : ℕ) → (p1 : inhab k l (ed F)) (p2 : inhab k l (ed G)) (n : Fin l) → (e : E F k l p1) → vmap (t F k l {p1} e n) ≡ (t G k l {p2} (emap k l p1 p2 e) n)
open _⇒_


record _≅_ (F : Hypergraph) (G : Hypergraph) : Set where
    field
        morph : F ⇒ G 
        vmap-bij : Bijective (λ x x₁ → V F) (λ x x₁ → V G) (vmap morph) 
        emap-bij : ∀ k l p → Bijective (λ x x₁ → E G k l p) (λ x x₁ → E G k l p) (emap morph k l)

open _≅_

record _≈_ {F G : Hypergraph} (f : F ⇒ G) (g : F ⇒ G) : Set₁ where
    field
        srcs : src f ≡ src g
        trgs : trg f ≡ trg g

open _≈_ 

same-inhabs : (A : Hypergraph) → ∀ k l      → inhab k l (ed A) ≡ inhab k l (ed A)
same-inhabs A k l = refl

id : (A : Hypergraph) → A ⇒ A
vmap (id A) x = x
emap (id A) k l p1 p2 x = x
sources-pred (id A) k l p1 p2 x = {!   !}
targets-pred (id A) = {!   !}

hyp-category : Category (lsucc lzero) lzero ((lsucc lzero))
Category.Obj hyp-category = Hypergraph
Category._⇒_ hyp-category = _⇒_
Category._≈_ hyp-category = _≈_
Category.id hyp-category = {!   !}
Category._∘_ hyp-category = {!   !}
Category.assoc hyp-category = {!   !}
Category.sym-assoc hyp-category = {!   !}
Category.identityˡ hyp-category = {!   !}
Category.identityʳ hyp-category = {!   !}
Category.identity² hyp-category = {!   !}
Category.equiv hyp-category = {!   !}
Category.∘-resp-≈ hyp-category = {!   !}  