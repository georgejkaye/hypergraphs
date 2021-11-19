This file defines the category of hypergraphs as a functor category.

\begin{code}

{-# OPTIONS --exact-split --safe #-}

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_) renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _+_ ; inj₁ to inl ; inj₂ to inr)
open import Data.Unit renaming (⊤ to 𝟙 ; tt to ∗)
open import Data.Empty
open import Data.Fin using (Fin)

open import Level renaming (zero to lzero ; suc to lsucc)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; cong ; sym)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core

open IsEquivalence renaming (refl to equiv-refl ; sym to equiv-sym ; trans to equiv-trans)

module Core.Category where

\end{code}

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

\begin{code}

Obj : Set
Obj = (ℕ × ℕ) + 𝟙

\end{code}

== Morphisms ==

For each object x = (k , l), there are k + l morphisms from x to ⋆.
The only other morphisms are the identity morphisms.

\begin{code}

_⇒_ : Obj → Obj → Set
inl a ⇒ inl b = a ≡ b
inl (k , l) ⇒ inr ∗ = k ≡ l
inr ∗ ⇒ inl b = ⊥
inr ∗ ⇒ inr ∗ = 𝟙

_≈_ : {A B : Obj} → A ⇒ B → A ⇒ B → Set
_≈_ {inl a} {inl .a} refl refl = a ≡ a
_≈_ {inl a} {inr ∗} refl refl = a ≡ a
_≈_ {inr ∗} {inr ∗} ∗ ∗ = 𝟙

id : (A : Obj) → A ⇒ A 
id (inl x) = refl
id (inr y) = ∗

\end{code}

Composition, associativity and identity are all fairly trivial once you pattern
match all the arguments.

\begin{code}

_∘_ : {A B C : Obj} → A ⇒ B → B ⇒ C → A ⇒ C
_∘_ {inl a} {inl .a} {inl .a} refl refl = refl
_∘_ {inl .(fst₁ , fst₁)} {inl (fst₁ , .fst₁)} {inr ∗} refl refl = refl
_∘_ {inl (fst₁ , .fst₁)} {inr ∗} {inr ∗} refl ∗ = refl
_∘_ {inr ∗} {inr ∗} {inr ∗} ∗ ∗ = ∗

assoc-l : {A B C D : Obj} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D) → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)
assoc-l {inl (fst₁ , snd₁)} {inl (.fst₁ , .snd₁)} {inl (.fst₁ , .snd₁)} {inl (.fst₁ , .snd₁)} refl refl refl = refl
assoc-l {inl (fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inr ∗} refl refl refl = refl
assoc-l {inl (fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inr ∗} {inr ∗} refl refl ∗ = refl
assoc-l {inl (fst₁ , .fst₁)} {inr ∗} {inr ∗} {inr ∗} refl ∗ ∗ = refl
assoc-l {inr ∗} {inr ∗} {inr ∗} {inr ∗} ∗ ∗ ∗ = ∗

assoc-r : {A B C D : Obj} → (f : A ⇒ B) → (g : B ⇒ C) → (h : C ⇒ D) → ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
assoc-r {inl (fst₁ , snd₁)} {inl (.fst₁ , .snd₁)} {inl (.fst₁ , .snd₁)} {inl (.fst₁ , .snd₁)} refl refl refl = refl
assoc-r {inl (fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inr ∗} refl refl refl = refl
assoc-r {inl (fst₁ , .fst₁)} {inl (.fst₁ , .fst₁)} {inr ∗} {inr ∗} refl refl ∗ = refl
assoc-r {inl (fst₁ , .fst₁)} {inr ∗} {inr ∗} {inr ∗} refl ∗ ∗ = refl
assoc-r {inr ∗} {inr ∗} {inr ∗} {inr ∗} ∗ ∗ ∗ = ∗

identity-l : {A B : Obj} → (f : A ⇒ B) → (f ∘ id B) ≈ f
identity-l {inl (fst₁ , snd₁)} {inl (.fst₁ , .snd₁)} refl = refl
identity-l {inl (fst₁ , .fst₁)} {inr ∗} refl = refl
identity-l {inr ∗} {inr ∗} ∗ = ∗

identity-r : {A B : Obj} → (f : A ⇒ B) → (id A ∘ f) ≈ f
identity-r {inl (fst₁ , snd₁)} {inl (.fst₁ , .snd₁)} refl = refl
identity-r {inl (fst₁ , .fst₁)} {inr ∗} refl = refl
identity-r {inr ∗} {inr ∗} ∗ = ∗

identity-2 : {A : Obj} → (id A ∘ id A) ≈ id A
identity-2 {inl x} = refl
identity-2 {inr y} = ∗

\end{code}

We want to show that ≈ is an equivalence relation.

\begin{code}

≈-refl : {A B : Obj} → {f : A ⇒ B} → f ≈ f
≈-refl {inl x} {inl .x} {refl} = refl
≈-refl {inl (fst₁ , .fst₁)} {inr y} {refl} = refl
≈-refl {inr y} {inl x} {()}
≈-refl {inr y} {inr y₁} {∗} = ∗

≈-sym : {A B : Obj} → {f g : A ⇒ B} → f ≈ g → g ≈ f
≈-sym {inl x₁} {inl .x₁} {refl} {refl} x = refl
≈-sym {inl (fst₁ , .fst₁)} {inr y} {refl} {refl} refl = refl
≈-sym {inr y} {inr y₁} x = ∗

≈-trans : {A B : Obj} → {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
≈-trans {inl x} {inl .x} {refl} {refl} {refl} refl refl = refl
≈-trans {inl (fst₁ , .fst₁)} {inr y} {refl} {refl} {refl} refl refl = refl
≈-trans {inr y} {inr y₁} {∗} {∗} {∗} ∗ ∗ = ∗

\end{code}

Finally, 

\begin{code}

∘-resp-≈ : {A B C : Obj} → {f h : A ⇒ B} → {g k : B ⇒ C} → (f ∘ g) ≈ (h ∘ k)
∘-resp-≈ {inl x} {inl .x} {inl .x} {refl} {refl} {refl} {refl} = refl
∘-resp-≈ {inl (fst₁ , .fst₁)} {inl .(fst₁ , fst₁)} {inr y} {refl} {refl} {refl} {refl} = refl
∘-resp-≈ {inl (fst₁ , .fst₁)} {inr y} {inr y₁} {refl} {refl} {∗} {∗} = refl
∘-resp-≈ {inr y} {inr y₁} {inr y₂} {∗} {∗} {∗} {∗} = ∗

\end{code}

We can can bundle everything together to make a category.

\begin{code}

X : Category lzero lzero lzero
Category.Obj X = Obj
Category._⇒_ X = _⇒_
Category._≈_ X = _≈_
Category.id X {A} = id A
Category._∘_ X {A} {B} {C} f g = g ∘ f
Category.assoc X {A} {B} {C} {D} {f} {g} {h} = assoc-l f g h
Category.sym-assoc X {A} {B} {C} {D} {f} {g} {h} = assoc-r f g h
Category.identityˡ X {A} {B} {f} = identity-l f
Category.identityʳ X {A} {B} {f} = identity-r f
Category.identity² X {A} = identity-2
Category.equiv X = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }
Category.∘-resp-≈ X f g = ∘-resp-≈ 

\end{code}