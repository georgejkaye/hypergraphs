{-# OPTIONS --exact-split --safe #-}

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr)
open import Data.Unit renaming (⊤ to 𝟙 ; tt to ∗)
open import Data.Empty
open import Data.Fin using (Fin)

open import Level renaming (zero to lzero ; suc to lsucc)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; sym)

open import Categories.Category.Core

module Core.Core where

open Category

X : Category lzero lzero lzero
Obj X = (ℕ × ℕ) + 𝟙
(X ⇒ inl x) (inl y) = x ≡ y
(X ⇒ inl (k , l)) (inr y) = Fin (k +ℕ l)
(X ⇒ inr x) (inl y) = ⊥
(X ⇒ inr x) (inr y) = 𝟙
_≈_ X {inl x} {inl .x} refl refl = x ≡ x
_≈_ X {inl x} {inr y} a b = a ≡ b
_≈_ X {inr x} {inr y} ∗ ∗ = 𝟙
id X {inl x} = refl
id X {inr ∗} = ∗
_∘_ X {inl a} {inl b} {inl c} g f = trans f g
_∘_ X {inl a} {inl .a} {inr c} g refl = g
_∘_ X {inl a} {inr b} {inr c} g f = f
_∘_ X {inr a} {inr b} {inr c} g f = ∗
assoc X {inl a} {inl .a} {inl .a} {inl .a} {refl} {refl} {refl} = refl
assoc X {inl a} {inl .a} {inl .a} {inr ∗} {refl} {refl} {h} = {!  !}
assoc X {inl a} {inl .a} {inr c} {inr d} {refl} {g} {∗} = {!  !}
assoc X {inl (fst₁ , snd₁)} {inr ∗} {inr ∗} {inr ∗} {f} {∗} {∗} = {!   !}
assoc X {inr a} {inr b} {inr c} {inr d} {∗} {∗} {∗} = ∗
sym-assoc X = {!   !}
identityˡ X = {!   !}
identityʳ X = {!   !}
identity² X = {!   !}
equiv X = {!   !}
∘-resp-≈ X = {!   !}  

-- _∘_ X {inl a} {inl b} {inl c} g f = trans f g
-- _∘_ X {inl a} {inl b} {inr c} g f = p6 where 
--     p1 : ∀ {a b c d} → a ≡ c → b ≡ d → a +ℕ b ≡ c +ℕ d
--     p1 refl refl = refl
--     p2 : (a b : ℕ × ℕ) → a ≡ b → fst a ≡ fst b
--     p2 a b refl = refl
--     p3 : (a b : ℕ × ℕ) → a ≡ b → snd a ≡ snd b
--     p3 a b refl = refl
--     p4 : b ≡ a
--     p4 = sym f
--     p5 : fst b +ℕ snd b ≡ fst a +ℕ snd a
--     p5 = p1 (p2 b a p4) (p3 b a p4)
--     p6 : Fin (fst a +ℕ snd a)
--     p6 = fin-same g p5 