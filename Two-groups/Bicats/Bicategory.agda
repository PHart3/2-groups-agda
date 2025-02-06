{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

-- Warning: We define a bicategory as a (2,1)-category with paths as 2-cells.

module Bicategory where

module _ (j : ULevel) where

  record BicatStr {i} (B₀ : Type i) : Type (lmax i (lsucc j)) where
    infixr 82 _◻_
    field
      hom : B₀ → B₀ → Type j
      instance {{hom-trunc}} : {a b : B₀} → has-level 1 (hom a b)
      id₁ : (a : B₀) → hom a a
      _◻_ : {a b c : B₀} → hom a b → hom b c → hom a c
      lamb : {a b : B₀} (f : hom a b) → id₁ a ◻ f == f  -- "λ" is built-in term
      ρ : {a b : B₀} (f : hom a b) → f ◻ id₁ b == f
      α : {a b c d : B₀} (f : hom a b) (g : hom b c) (h : hom c d) → f ◻ g ◻ h == (f ◻ g) ◻ h
      id₁-l : {a b : B₀} {f g : hom a b} (θ : f == g) → ap (λ m → id₁ a ◻ m) θ ∙ lamb g == lamb f ∙ θ  
      id₁-r : {a b : B₀} {f g : hom a b} (θ : f == g) → ap (λ m → m ◻ id₁ b) θ ∙ ρ g == ρ f ∙ θ
      α-law1 : {a b c d : B₀} (f : hom a b) (g : hom b c) {h i : hom c d} (θ : h == i)
        → ap (λ m → f ◻ m) (ap (λ m → g ◻ m) θ) ∙ α f g i == α f g h ∙ ap (λ m → (f ◻ g) ◻ m) θ
      α-law2 : {a b c d : B₀} (f : hom a b) {g h : hom b c} {i : hom c d} (θ : g == h)
        → ap (λ m → f ◻ m) (ap (λ m → m ◻ i) θ) ∙ α f h i == α f g i ∙ ap (λ m → m ◻ i) (ap (λ m → f ◻ m) θ)
      α-law3 : {a b c d : B₀} {f g : hom a b} (h : hom b c) (i : hom c d) (θ : f == g)
        → ap (λ m → m ◻ h ◻ i) θ ∙ α g h i == α f h i ∙ ap (λ m → m ◻ i) (ap (λ m → m ◻ h) θ)
      tri-bc : {a b c : B₀} (f : hom a b) (g : hom b c)
        → α f (id₁ b) g ∙ ap (λ m → m ◻ g) (ρ f) == ap (λ m → f ◻ m) (lamb g) 
      pent-bc : {a b c d e : B₀} (f : hom a b) (g : hom b c) (h : hom c d) (i : hom d e)
        → α f g (h ◻ i) ∙ α (f ◻ g) h i == ap (λ m → f ◻ m) (α g h i) ∙ α f (g ◻ h) i ∙ ap (λ m → m ◻ i) (α f g h)

open BicatStr {{...}}

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  record PsfunctorStr (F₀ : B₀ → C₀) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      F₁ : {a b : B₀} → hom a b → hom (F₀ a) (F₀ b)
      F-id₁ : {a : B₀} → id₁ (F₀ a) == F₁ (id₁ a)
      F-◻ : {a b c : B₀} (f : hom a b) (g : hom b c)
        → _◻_ {{ξC}} (F₁ f) (F₁ g) == F₁ (_◻_ {{ξB}} f g)  -- somehow Agda gets stuck on the two instance candidates
      -- F-wh1 : 
      -- F-wh2 : 
      -- F-λ : 
      -- F-ρ : 
      -- F-α : 
