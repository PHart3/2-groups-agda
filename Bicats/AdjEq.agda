{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory

module AdjEq where

open BicatStr {{...}}

-- adjoint equivalence structure on a 1-cell of a bicategory

module _ {i j} {B₀ : Type i} where

  record Adjequiv {{_ : BicatStr j B₀}} {a b : B₀} (f : hom a b) : Type (lmax i j) where
    field
      inv : hom b a
      eta : id₁ a == inv ◻ f
      eps : id₁ b == f ◻ inv
      coher-map : ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps
      coher-inv : lamb inv ∙ ap (λ m → m ◻ inv) eta == ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv

  AdjEquiv : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
  AdjEquiv ξB a b = Σ (hom {{ξB}} a b) (λ f → Adjequiv {{ξB}} f)
