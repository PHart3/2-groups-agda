{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import K-hom-ind
open import KFunctor
open import KFunctor-comp-aux4

-- K₂-map respects composition

module KFunctor-comp where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) where

    K₂-map-∘-hnat : (x : G₁) →
      ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x)
        ==
      ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x) ∙ idp
    K₂-map-∘-hnat x =
    -- ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x)
      K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x ∙
    -- loop G₃ (f₂ (f₁ x))
      ! (K₂-map-β-pts σ₂ (f₁ x)) ∙
    -- ap (K₂-map σ₂) (loop G₂ (f₁ x))
      ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ∙
    -- ap (K₂-map σ₂) (ap (K₂-map σ₁) (loop G₁ x))
      ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ∙
    -- ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)
      ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x)))
    -- ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x) ∙ idp

    open K₂-map-∘-aux σ₁ σ₂

    private
      map₁ = K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})
      map₂ = K₂-map σ₂ ∘ K₂-map σ₁

    -- K₂-map respects composition
    K₂-map-∘ : K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) ∼ K₂-map σ₂ ∘ K₂-map σ₁
    K₂-map-∘ =
      K₂-∼-ind
        map₁ map₂
        idp
        K₂-map-∘-hnat
        K₂-map-∘-coher
