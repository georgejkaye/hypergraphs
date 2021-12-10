{-# OPTIONS --exact-split --safe #-}

open import Categories.Category

open import Data.Nat using (zero ; ℕ) renaming (suc to succ)
open import Data.Fin using (Fin)
open import Level using () renaming (zero to lzero ; suc to lsucc)
open import Function using (_∘′_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

module Core.FinSet where

record AllFins : Set₁ where
    field
        n : ℕ

    fin : Set
    fin = Fin n

femp : AllFins
AllFins.n femp = zero

fone : AllFins
AllFins.n fone = succ zero

open AllFins

FinSet : Category (lsucc lzero) lzero lzero
FinSet = record
  { Obj = AllFins
  ; _⇒_ = λ x y → (fin x) → (fin y)
  ; _≈_ = λ f g → ∀ {x} → f x ≡ g x
  ; id = idf
  ; _∘_ = _∘′_
  ; assoc = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  ; equiv     = record
    { refl  = ≡.refl
    ; sym   = λ eq → ≡.sym eq
    ; trans = λ eq₁ eq₂ → ≡.trans eq₁ eq₂
    }
  ; ∘-resp-≈  = resp
  }
  where resp : ∀ {A B C : AllFins} {f h : (fin B) → (fin C)} {g i : (fin A) → (fin B)} →
                 ({x : (fin B)} → f x ≡ h x) →
                 ({x : (fin A)} → g x ≡ i x) → {x : (fin A)} → f (g x) ≡ h (i x)
        resp {h = h} eq₁ eq₂ = ≡.trans eq₁ (≡.cong h eq₂)
