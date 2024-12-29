{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpHom where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (τ : id == map id) where

  rho-to-lam : (x : G₁)
    → ap (λ z → mu z (map x)) τ ∙ map-comp id x ∙ ap map (lam x) == lam (map x)
    → ap (mu (map x)) τ ∙ map-comp x id ∙ ap map (rho x) == rho (map x)
  rho-to-lam x ρ = {!!}


  -- equivalence between the two definitions of 2-group morphism
