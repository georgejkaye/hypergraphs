This file defines the category of hypergraphs as a functor category.

```

{-# OPTIONS --exact-split --safe #-}

open import Agda.Builtin.Bool
open import Data.Bool using (_∧_ ; _∨_ ; if_then_else_)

open import Data.Nat using (ℕ ; zero ; suc ; _≡ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr)
open import Data.Unit renaming (⊤ to 𝟙 ; tt to ∗)
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.String using (String)
open import Data.List using (List ; _∷_ ; [] ; length ; filter)

open import Level renaming (zero to lzero ; suc to lsucc)

open import Relation.Nullary
open import Relation.Unary using (Decidable ; Pred)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; sym)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core

open import Core.FinSet

open IsEquivalence renaming (refl to equiv-refl ; sym to equiv-sym ; trans to equiv-trans)

module Core.Category where

open AllFins


```

We want to define a category of hypergraphs. We could just go ahead and define
it directly in terms of vertices, edges, sources and targets, but we will take
a slightly more sophisticated construction by building it as a functor category
from some 'template category' into Set. This gives us the added bonus of making
Hyp adhesive by definition, as Set is adhesive and adhesivity is preserved by
functor categories.

First we define the 'template category' of hypergraphs X. This category will
determine the relationships between the vertices and the edges.

== Objects ==

For each k,l ∈ ℕ, there is an object (k , l) to represent edges with k sources
and l targets. Then there is an additional object ⋆ to represent vertices.

```

Obj : Set
Obj = (ℕ × ℕ) + 𝟙

```

== Morphisms ==

For each object x = (k , l), there are k + l morphisms from x to ⋆.
The only other morphisms are the identity morphisms.

```

_⇒_ : Obj → Obj → Set
inl a ⇒ inl b = a ≡ b
inl (k , l) ⇒ inr ∗ = Fin (k +ℕ l)
inr ∗ ⇒ inl b = ⊥
inr ∗ ⇒ inr ∗ = 𝟙

_≈_ : {A B : Obj} → A ⇒ B → A ⇒ B → Set
_≈_ {inl x} {inl .x} refl refl = x ≡ x
_≈_ {inl x} {inr ∗} f g = f ≡ g
_≈_ {inr x} {inr y} ∗ ∗ = 𝟙

infix  4 _≈_ _⇒_

id : {A : Obj} → A ⇒ A
id {inl x} = refl
id {inr ∗} = ∗

```

Composition, associativity and identity are all fairly trivial once you pattern
match all the arguments.

```

_·_ : {A B C : Obj} → A ⇒ B → B ⇒ C → A ⇒ C
_·_ {inl x} {inl .x} {inl .x} refl refl = refl
_·_ {inl x} {inl .x} {inr ∗} refl g = g
_·_ {inl x} {inr ∗} {inr ∗} f ∗ = f
_·_ {inr ∗} {inr ∗} {inr ∗} ∗ ∗ = ∗

infixr 9 _·_

assoc-l : {A B C D : Obj} → {f : A ⇒ B} → {g : B ⇒ C} → {h : C ⇒ D} → f · (g · h) ≈ (f · g) · h
assoc-l {inl x} {inl .x} {inl .x} {inl .x} {refl} {refl} {refl} = refl
assoc-l {inl x} {inl .x} {inl .x} {inr ∗} {refl} {refl} {h} = refl
assoc-l {inl x} {inl y} {inr ∗} {inr ∗} {f} {g} {∗} = refl
assoc-l {inl x} {inr ∗} {inr ∗} {inr ∗} {f} {∗} {∗} = refl
assoc-l {inr ∗} {inr ∗} {inr ∗} {inr ∗} {∗} {∗} {∗} = ∗

assoc-r : {A B C D : Obj} → {f : A ⇒ B} → {g : B ⇒ C} → {h : C ⇒ D} → (f · g) · h ≈ f · (g · h)
assoc-r {inl x} {inl .x} {inl .x} {inl .x} {refl} {refl} {refl} = refl
assoc-r {inl x} {inl .x} {inl .x} {inr ∗} {refl} {refl} {h} = refl
assoc-r {inl x} {inl .x} {inr ∗} {inr ∗} {refl} {g} {∗} = refl
assoc-r {inl x} {inr ∗} {inr ∗} {inr ∗} {f} {∗} {∗} = refl
assoc-r {inr ∗} {inr ∗} {inr ∗} {inr ∗} {∗} {∗} {∗} = ∗

identity-l : {A B : Obj} → {f : A ⇒ B} → f · id ≈ f
identity-l {inl x} {inl .x} {refl} = refl
identity-l {inl x} {inr ∗} {f} = refl
identity-l {inr ∗} {inr ∗} {∗} = ∗

identity-r : {A B : Obj} → {f : A ⇒ B} → id · f ≈ f
identity-r {inl x} {inl .x} {refl} = refl
identity-r {inl x} {inr ∗} {f} = refl
identity-r {inr ∗} {inr ∗} {∗} = ∗

identity-2 : {A : Obj} → (id {A} · id {A}) ≈ id {A}
identity-2 {inl x} = refl
identity-2 {inr ∗} = ∗

```

We want to show that ≈ is an equivalence relation.

```

≈-refl : {A B : Obj} → {f : A ⇒ B} → f ≈ f
≈-refl {inl x} {inl .x} {refl} = refl
≈-refl {inl x} {inr ∗} {f} = refl
≈-refl {inr ∗} {inr ∗} {∗} = ∗

≈-sym : {A B : Obj} → {f g : A ⇒ B} → f ≈ g → g ≈ f
≈-sym {inl x} {inl .x} {refl} {refl} refl = refl
≈-sym {inl x} {inr ∗} {f} {.f} refl = refl
≈-sym {inr ∗} {inr ∗} {∗} {∗} ∗ = ∗

≈-trans : {A B : Obj} → {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
≈-trans {inl x} {inl .x} {refl} {refl} {refl} refl refl = refl
≈-trans {inl x} {inr ∗} {f} {.f} {.f} refl refl = refl
≈-trans {inr ∗} {inr ∗} {∗} {∗} {∗} ∗ ∗ = ∗

```

Finally, composition must respect ≈.

```

·-resp-≈ : {A B C : Obj} → {f h : A ⇒ B} → {g k : B ⇒ C} → f ≈ h → g ≈ k → (f · g) ≈ (h · k)
·-resp-≈ {inl x} {inl .x} {inl .x} {refl} {refl} {refl} {refl} refl refl = refl
·-resp-≈ {inl x} {inl .x} {inr ∗} {refl} {refl} {g} {.g} p refl = refl
·-resp-≈ {inl x} {inr ∗} {inr ∗} {f} {.f} {g} {k} refl ∗ = refl
·-resp-≈ {inr ∗} {inr ∗} {inr ∗} {∗} {∗} {∗} {∗} ∗ ∗ = ∗

```

We can can bundle everything together to make a category.

```

X : Category lzero lzero lzero
X = record
    { Obj = Obj
    ; _⇒_ = λ x y → x ⇒ y
    ; _≈_ = λ f g → f ≈ g
    ; id = id
    ; _∘_ = λ f g → g · f
    ; assoc = assoc-l
    ; sym-assoc = assoc-r
    ; identityˡ = identity-l
    ; identityʳ = identity-r
    ; identity² = identity-2
    ; equiv = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }
    ; ∘-resp-≈ = λ p q → ·-resp-≈ q p
    }

```

Hypergraphs are defined as a functor category from X to Set.

```
open import Categories.Functor.Core
open import Categories.Category.Construction.Functors
open Functor

HypC : Category (lsucc lzero) lzero lzero
HypC = Functors X FinSet

```

To make our life a bit easier, we define a function to grab out the map
from X to Set. These are the actual 'hypergraphs'.

```
Hyp : Category.Obj HypC → (Category.Obj X → AllFins)
Hyp x = Functor.F₀ x

V : Category.Obj HypC → AllFins
V x = (Functor.F₀ x) (inr ∗)

```

A hypergraph signature is a hypergraph with one vertex that acts as the source
and target for all hyperedges.

We define a function that gets the number of vertices in a hypergraph.

```

vs : Category.Obj HypC → ℕ
vs x = AllFins.n (V x)

record Label (k : ℕ) (l : ℕ) : Set where
    field
        name : String

open Label

record Signature : Set where
    field
        size : ℕ
        labels : (k : ℕ) → (l : ℕ) → List (Label k l)

open Signature

sig-F₀ : Signature → Category.Obj X → AllFins
sig-F₀ sig (inl (k , l)) = finx {!  !}
sig-F₀ sig (inr y) = {!   !}

signature-graph : Signature → Category.Obj HypC
F₀ (signature-graph x) = {!   !}
F₁ (signature-graph x) = {!   !}
identity (signature-graph x)  = {!   !}
homomorphism (signature-graph x) = {!   !}
F-resp-≈ (signature-graph x) = {!   !}

```
