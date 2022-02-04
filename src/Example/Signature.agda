open import Core.Category

open import Data.Product using (_,_)
open import Data.List using (List ; _∷_ ; [] ; [_] )
open import Data.Nat
open import Data.List.Relation.Unary.Any using (there ; here)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

module Example.Signature where

open Signature

and : Label 2 1
and = record { name = "and" }

or : Label 2 1
or = record { name = "or" }

not : Label 1 1
not = record { name = "not" }

Σ⋆ : Signature
occupied Σ⋆ = ( 1 , 1 ) ∷ ( 2 , 1 ) ∷ []
labels Σ⋆ 1 1 (here _≡_) = [ not ]
labels Σ⋆ 2 1 (there (here refl)) = and ∷ or ∷ []