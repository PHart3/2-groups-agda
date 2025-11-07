{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory

module AdjEq where

open BicatStr {{...}}

-- adjoint equivalence structure on a 1-cell of a bicategory

module _ {i j} {B₀ : Type i} where

  record Adjequiv {{_ : BicatStr j B₀}} {a b : B₀} (f : hom a b) : Type (lmax i j) where
    constructor Adj-eqv
    field
      inv : hom b a
      eta : id₁ a == inv ◻ f
      eps : id₁ b == f ◻ inv
      coher-map : ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps
      coher-inv : ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv == lamb inv ∙ ap (λ m → m ◻ inv) eta

  AdjEquiv : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
  AdjEquiv ξB a b = Σ (hom {{ξB}} a b) (λ f → Adjequiv {{ξB}} f)

  module _ {{ξB : BicatStr j B₀}} where

    open Adjequiv

    AdjEq-id₁ : {a : B₀} → AdjEquiv ξB a a
    fst (AdjEq-id₁ {a}) = id₁ a
    inv (snd (AdjEq-id₁ {a})) = id₁ a
    eta (snd (AdjEq-id₁ {a})) = lamb (id₁ a)
    eps (snd (AdjEq-id₁ {a})) = ρ (id₁ a)
    coher-map (snd (AdjEq-id₁ {a})) = {!!}
    coher-inv (snd (AdjEq-id₁ {a})) = {!!}

    AdjEq-rev :  {a b : B₀} → AdjEquiv ξB a b → AdjEquiv ξB b a
    fst (AdjEq-rev (f , ae)) = inv ae
    inv (snd (AdjEq-rev (f , ae))) = f
    eta (snd (AdjEq-rev (f , ae))) = eps ae
    eps (snd (AdjEq-rev (f , ae))) = eta ae
    coher-map (snd (AdjEq-rev (f , ae))) = coher-inv ae
    coher-inv (snd (AdjEq-rev (f , ae))) = coher-map ae

    AdjEq-rev-≃ :  {a b : B₀} → AdjEquiv ξB a b ≃ AdjEquiv ξB b a
    AdjEq-rev-≃ = equiv AdjEq-rev AdjEq-rev (λ _ → idp) λ _ → idp

  -- (globally) univalent bicategories

  ==-to-adjeq : {{ξB : BicatStr j B₀}} {a b : B₀} → a == b → AdjEquiv ξB a b
  ==-to-adjeq idp = AdjEq-id₁

  is-univ-bc : BicatStr j B₀ → Type (lmax i j)
  is-univ-bc ξB = (a b : B₀) → is-equiv (==-to-adjeq {{ξB}} {a} {b})
