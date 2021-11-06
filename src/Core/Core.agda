{-# OPTIONS --exact-split --safe #-}

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr)
open import Data.Unit renaming (⊤ to 𝟙 ; tt to ∗)
open import Data.Empty
open import Data.Fin using (Fin)

open import Level renaming (zero to lzero ; suc to lsucc)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong)

open import Categories.Category.Core

module Core.Core where

open Category

fin-same : ∀ {x y} → Fin x → x ≡ y → Fin y
fin-same f refl = f

data ismorph {A : Set} : A → A → Set where
    same : (x y : A) → x ≡ y → ismorph x y

X : Category {!  !} {!   !} {!   !}
Obj X = ℕ × ℕ + 𝟙
(X ⇒ inl x) (inl y) = x ≡ y
(X ⇒ inl (k , l)) (inr y) = Fin (k +ℕ l)
(X ⇒ inr x) (inl y) = ⊥
(X ⇒ inr x) (inr y) = 𝟙
_≈_ X = λ f g → ⊥
id X {inl x} = refl
id X {inr ∗} = ∗
_∘_ X {inl x} {inl y} {inl z} f g = trans g f
_∘_ X {inl x} {inl y} {inr z} f g = fin-same f (p1 g) where
    p1 : x ≡ y → fst y +ℕ snd y ≡ fst x +ℕ snd x
    p1 refl = refl
_∘_ X {inl x} {inr y} {inr z} f g = g
_∘_ X {inr x} {inr y} {inr z} f g = ∗
assoc X = {!   !}
sym-assoc X = {!   !}
identityˡ X = {!   !}
identityʳ X = {!   !}
identity² X = {!   !}
equiv X = {!   !}
∘-resp-≈ X = {!   !}  