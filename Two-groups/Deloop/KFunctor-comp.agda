{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor

-- K₂-map respects composition

module KFunctor-comp where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) where

    -- K₂-map respects composition
    K₂-map-∘ : K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) ∼ K₂-map σ₂ ∘ K₂-map σ₁
    K₂-map-∘ = K₂-∼-ind (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (K₂-map σ₂ ∘ K₂-map σ₁) idp {!!} {!!}
