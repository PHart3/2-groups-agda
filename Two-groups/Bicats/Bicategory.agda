{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

-- Nota bene: We define a bicategory as a (2,1)-category with paths as 2-cells.

module Bicategory where

module _ (j : ULevel) where

  record PreBicatStr {i} (B₀ : Type i) : Type (lmax i (lsucc j)) where
    infixr 82 _◻_
    field
      hom : B₀ → B₀ → Type j
      id₁ : (a : B₀) → hom a a
      _◻_ : {a b c : B₀} → hom b c → hom a b → hom a c
      ρ : {a b : B₀} (f : hom a b) → f == f ◻ id₁ a
      lamb : {a b : B₀} (f : hom a b) → f == id₁ b ◻ f
      α : {a b c d : B₀} (h : hom c d) (g : hom b c) (f : hom a b) → h ◻ g ◻ f == (h ◻ g) ◻ f
      id₁-r : {a b : B₀} {f g : hom a b} (θ : g == f) →  ρ g ∙ ap (λ m → m ◻ id₁ a) θ == θ ∙ ρ f  
      id₁-l : {a b : B₀} {f g : hom a b} (θ : g == f) →  lamb g ∙ ap (λ m → id₁ b ◻ m) θ == θ ∙ lamb f
      α-law1 : {a b c d : B₀} (f : hom a b) (g : hom b c) {h i : hom c d} (θ : h == i)
        → α h g f ∙ ap (λ m → m ◻ f) (ap (λ m → m ◻ g) θ) == ap (λ m → m ◻ (g ◻ f)) θ ∙ α i g f
      α-law2 : {a b c d : B₀} (f : hom a b) {g h : hom b c} {i : hom c d} (θ : g == h)
        → α i g f ∙ ap (λ m → m ◻ f) (ap (λ m → i ◻ m) θ) == ap (λ m → i ◻ m) (ap (λ m → m ◻ f) θ) ∙ α i h f
      α-law3 : {a b c d : B₀} {f g : hom a b} (h : hom b c) (i : hom c d) (θ : f == g)
        → α i h f ∙ ap (λ m → (i ◻ h) ◻ m) θ == ap (λ m → i ◻ m) (ap (λ m → h ◻ m) θ) ∙ α i h g 
      tri-bc : {a b c : B₀} (f : hom a b) (g : hom b c)
        → ap (λ m → g ◻ m) (lamb f) ∙ α g (id₁ b) f == ap (λ m → m ◻ f) (ρ g)
      pent-bc : {a b c d e : B₀} (f : hom a b) (g : hom b c) (h : hom c d) (i : hom d e)
        →  α i h (g ◻ f) ∙ α (i ◻ h) g f == ap (λ m → i ◻ m) (α h g f) ∙ α i (h ◻ g) f ∙ ap (λ m → m ◻ f) (α i h g)
      instance {{hom-trunc}} : {a b : B₀} → has-level 1 (hom a b)

open PreBicatStr {{...}}

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : PreBicatStr j₁ B₀}} {{ξC : PreBicatStr j₂ C₀}} where

  record PsfunctorStr (F₀ : B₀ → C₀) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      F₁ : {a b : B₀} → hom a b → hom (F₀ a) (F₀ b)
      F-id₁ : (a : B₀) → F₁ (id₁ a) == id₁ (F₀ a)
      F-◻ : {a b c : B₀} (f : hom a b) (g : hom b c)
        → F₁ (_◻_ {{ξB}} g f) == _◻_ {{ξC}} (F₁ g) (F₁ f)  -- somehow Agda gets stuck on the two instance candidate 
      F-ρ : {a b : B₀} (f : hom a b) → ap F₁ (ρ f) ∙ F-◻ (id₁ a) f ∙ ap (λ m → F₁ f ◻ m) (F-id₁ a) == ρ (F₁ f)
      F-λ : {a b : B₀} (f : hom a b) → ap F₁ (lamb f) ∙ F-◻ f (id₁ b) ∙ ap (λ m → m ◻ F₁ f) (F-id₁ b) == lamb (F₁ f)
      F-α : {a b c d : B₀} (h : hom c d) (g : hom b c) (f : hom a b)
        →
        ! (ap (λ m → F₁ h ◻ m) (F-◻ f g)) ∙ ! (F-◻ (g ◻ f) h) ∙ ap F₁ (α h g f) ∙ F-◻ f (h ◻ g) ∙ ap (λ m → m ◻ F₁ f) (F-◻ g h)
          ==
        α (F₁ h) (F₁ g) (F₁ f)

-- composition and id

-- equivalences str between two pseudofucntors (skip pseudotransf definition itself)

-- biequiv strucutre between two bicats
