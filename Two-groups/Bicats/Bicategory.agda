{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

-- Warning: We define a bicategory as a (2,1)-category with paths as 2-cells.

module Bicategory where

module _ {i} (B₀ : Type i) where

  record BicatStr (j k : ULevel) : Type (lmax i (lmax (lsucc j) (lsucc k))) where
    infixr 82 _◻_
    field
      B₁ : B₀ → B₀ → Type j
      instance {{B₁-trunc}} : {a b : B₀} → has-level 1 (B₁ a b)
      id₁ : (a : B₀) → B₁ a a
      _◻_ : {a b c : B₀} → B₁ a b → B₁ b c → B₁ a c
      lamb : {a b : B₀} (f : B₁ a b) → id₁ a ◻ f == f  -- "λ" is built-in term
      ρ : {a b : B₀} (f : B₁ a b) → f ◻ id₁ b == f
      α : {a b c d : B₀} (f : B₁ a b) (g : B₁ b c) (h : B₁ c d) → f ◻ g ◻ h == (f ◻ g) ◻ h
      id₁-l : {a b : B₀} {f g : B₁ a b} (θ : f == g) → ap (λ m → id₁ a ◻ m) θ ∙ lamb g == lamb f ∙ θ  
      id₁-r : {a b : B₀} {f g : B₁ a b} (θ : f == g) → ap (λ m → m ◻ id₁ b) θ ∙ ρ g == ρ f ∙ θ
      α-law1 : {a b c d : B₀} (f : B₁ a b) (g : B₁ b c) {h i : B₁ c d} (θ : h == i)
        → ap (λ m → f ◻ m) (ap (λ m → g ◻ m) θ) ∙ α f g i == α f g h ∙ ap (λ m → (f ◻ g) ◻ m) θ
      α-law2 : {a b c d : B₀} (f : B₁ a b) {g h : B₁ b c} {i : B₁ c d} (θ : g == h)
        → ap (λ m → f ◻ m) (ap (λ m → m ◻ i) θ) ∙ α f h i == α f g i ∙ ap (λ m → m ◻ i) (ap (λ m → f ◻ m) θ)
      α-law3 : {a b c d : B₀} {f g : B₁ a b} (h : B₁ b c) (i : B₁ c d) (θ : f == g)
        → ap (λ m → m ◻ h ◻ i) θ ∙ α g h i == α f h i ∙ ap (λ m → m ◻ i) (ap (λ m → m ◻ h) θ)
      tri-bc : {a b c : B₀} (f : B₁ a b) (g : B₁ b c)
        → α f (id₁ b) g ∙ ap (λ m → m ◻ g) (ρ f) == ap (λ m → f ◻ m) (lamb g) 
      pent-bc : {a b c d e : B₀} (f : B₁ a b) (g : B₁ b c) (h : B₁ c d) (i : B₁ d e)
        → α f g (h ◻ i) ∙ α (f ◻ g) h i == ap (λ m → f ◻ m) (α g h i) ∙ α f (g ◻ h) i ∙ ap (λ m → m ◻ i) (α f g h)

module _ {i₁ i₂ j₁ j₂ k₁ k₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr B₀ j₁ k₁}} {{ξC : BicatStr C₀ j₂ k₂}} where

  record Psfunctor : Type (lmax i₁ (lmax (lmax j₁ k₁) (lmax i₂ (lmax j₂ k₂)))) where
    field
      map-pf : B₀ → C₀
      
