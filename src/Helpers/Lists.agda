{-# OPTIONS --exact-split --safe #-}

open import Data.List
open import Relation.Binary.PropositionalEquality

module Helpers.Lists where

data _in-list_ {A : Set} : A → List A → Set where
    in-head : ∀ a xs → a in-list (a ∷ xs) 
    in-cons : ∀ a x xs → a in-list xs → a in-list (x ∷ xs)

data _not-in-list_ {A : Set} : A → List A → Set where
    not-in-empty : ∀ a → a not-in-list []
    not-in-cons  : ∀ a x xs → a ≢ x → a not-in-list xs → a not-in-list (x ∷ xs) 