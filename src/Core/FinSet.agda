open import Categories.Category

open import Data.Fin using (Fin)
open import Level renaming (zero to lzero ; suc to lsucc)

module Core.FinSet where

FiniteSets : Set₁
FiniteSets = {!   !}

FinSet : Category (lsucc lzero) lzero lzero
Category.Obj FinSet = FiniteSets
Category._⇒_ FinSet = {!   !}
Category._≈_ FinSet = {!   !}
Category.id FinSet = {!   !}
Category._∘_ FinSet = {!   !}
Category.assoc FinSet = {!   !}
Category.sym-assoc FinSet = {!   !}
Category.identityˡ FinSet = {!   !}
Category.identityʳ FinSet = {!   !}
Category.identity² FinSet = {!   !}
Category.equiv FinSet = {!   !}
Category.∘-resp-≈ FinSet = {!   !}