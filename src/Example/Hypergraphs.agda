open import Data.Nat
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns
open import Data.Product
open import Data.List using (List ; [] ; _∷_)
open import Data.Sum.Base using () renaming (inj₁ to inl ; inj₂ to inr)
open import Data.Empty

open import Core.Hypergraph
open import Core.Morphism
open import Core.Properties
open import Relation.Binary.PropositionalEquality

module Example.Hypergraphs where

open Hypergraph
open _⇒_

vert : Hypergraph [] 
v vert = 1
e vert k l = 0
s vert k l () n
t vert k l () n

single-edge : Hypergraph  ((1 , 2) ∷ [] )
v single-edge = 3
e single-edge 0 0 = 0
e single-edge 0 (suc l) = 0
e single-edge (suc k) zero = 0
e single-edge 1 1 = 0
e single-edge 1 2 = 1
e single-edge 1 (suc (suc (suc l))) = 0
e single-edge (suc (suc k)) (suc l) = 0
s single-edge (suc zero) (suc (suc zero)) 0F 0F = 0F
s single-edge (suc (suc k)) (suc (suc (suc l))) () n
t single-edge (suc zero) (suc (suc zero)) x 0F = 1F
t single-edge (suc zero) (suc (suc zero)) x 1F = 2F
t single-edge (suc (suc k)) (suc l) () n

morph : vert ⇒ example
vmap morph 0F = 0F
sources-pres morph zero zero p1 p2 () x
sources-pres morph zero (suc l) p1 p2 () x
targets-pres morph k l p1 p2 n ()

morph-1 : single-edge ⇒ example
vmap morph-1 0F = 1F
vmap morph-1 1F = 2F
vmap morph-1 2F = 3F
emap morph-1 zero zero p1 p2 ()
emap morph-1 zero (suc l) p1 p2 ()
emap morph-1 1 2 p1 p2 0F = 0F
sources-pres morph-1 1 2 p1 p2 0F 0F = refl
targets-pres morph-1 1 2 p1 p2 0F 0F = refl
targets-pres morph-1 1 2 p1 p2 1F 0F = refl

open monogamous

-- 0F not-in-list targets single-edge 1 2 0F

one-edge-monog : monogamous single-edge
left one-edge-monog 0F = lm 0F (inr (λ k l p e → ist 0F e (p1 k l p e))) where
    p1 : ∀ k l p e → 0F not-in-list (targets single-edge k l p e)
    p1 zero zero p ()
    p1 zero (suc zero) p ()
    p1 zero (suc (suc l)) p ()
    p1 (suc zero) (suc (suc zero)) p 0F = not-in-cons 0F 1F (2F ∷ []) (λ ()) (not-in-cons 0F 2F [] (λ ()) (not-in-empty 0F))
left one-edge-monog 1F = lm 1F (inl (1 , (2 , (λ e → 0F , (ist 1F 0F (in-head 1F (2F ∷ [])) , λ where 0F → λ x → ⊥-elim (x refl) )))))
left one-edge-monog 2F = lm 2F (inl (1 , (2 , (λ e → 0F , (ist 2F 0F (in-cons 2F 1F (2F ∷ []) (in-head 2F []))) , λ where 0F → λ x → ⊥-elim (x refl) ))))
right one-edge-monog 0F = rm 0F (inl (1 , (2 , (λ p → 0F , ((iss 0F 0F (in-head 0F [])) , (λ where 0F → λ x → ⊥-elim ((x refl))))))))
right one-edge-monog 1F = rm 1F (inr {!   !}) where 
    p2 : ∀ k l p e → 1F not-in-list (sources single-edge)
right one-edge-monog 2F = rm 2F (inr {!   !})

