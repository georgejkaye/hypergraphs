open import Data.Nat
open import Data.Fin using () renaming (suc to fsuc)
open import Data.Fin.Patterns

open import Core.Hypergraph
open import Core.Morphism
open import Relation.Binary.PropositionalEquality

module Example.Hypergraphs where

open Hypergraph
open _⇒_

vert : Hypergraph 
v vert = 1
e vert k l = 0
s vert () n p
t vert () n x₁ 

single-edge : Hypergraph
v single-edge = 3
e single-edge 0 0 = 0
e single-edge 0 (suc l) = 0
e single-edge (suc k) zero = 0
e single-edge 1 1 = 0
e single-edge 1 2 = 1
e single-edge 1 (suc (suc (suc l))) = 0
e single-edge (suc (suc k)) (suc l) = 0
s single-edge {0} {0} () n p
s single-edge {0} {1} () n p
s single-edge {0} {2} () n p
s single-edge {1} {0} () n p
s single-edge {1} {1} () n p
s single-edge {1} {2} 0F zero (s≤s p) = 0F
s single-edge {suc (suc zero)} {suc (suc zero)} () n p
s single-edge {suc (suc zero)} {suc (suc (suc l))} () n p
s single-edge {suc (suc (suc k))} {suc (suc zero)} () n p
s single-edge {suc (suc (suc k))} {suc (suc (suc l))} () n p
t single-edge {0} {0} () n p
t single-edge {0} {1} () n p
t single-edge {0} {2} () n p
t single-edge {1} {0} () n p
t single-edge {1} {1} () n p
t single-edge {1} {2} 0F zero (s≤s z≤n) = 1F
t single-edge {1} {2} 0F (suc zero) (s≤s (s≤s p)) = 2F
t single-edge {suc (suc zero)} {suc (suc zero)} () n p
t single-edge {suc (suc zero)} {suc (suc (suc l))} () n p
t single-edge {suc (suc (suc k))} {suc (suc zero)} () n p
t single-edge {suc (suc (suc k))} {suc (suc (suc l))} () n p

morph : vert ⇒ example
vmap morph 0F = 0F
emap morph ()
sources-pres morph zero (s≤s p) ()
sources-pres morph (suc n) (s≤s p) ()
targets-pres morph zero (s≤s p) ()
targets-pres morph (suc n) (s≤s p) ()

morph-1 : single-edge ⇒ example
vmap morph-1 0F = 1F
vmap morph-1 1F = 2F
vmap morph-1 2F = 3F
emap morph-1 {zero} {suc (suc k)} ()
emap morph-1 {suc zero} {suc (suc zero)} 0F = 0F
sources-pres morph-1 {suc zero} {suc (suc zero)} zero (s≤s z≤n) 0F = refl
targets-pres morph-1 {suc zero} {suc (suc zero)} zero (s≤s z≤n) 0F = refl
targets-pres morph-1 {suc zero} {suc (suc zero)} (suc zero) (s≤s (s≤s z≤n)) 0F = refl