{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

-- K₂-map respects composition

module KFunctor-comp-aux1 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) where

    open WkMag hiding (mu)

    abstract
      K₂-map-∘-coher0 : (x y : G₁) →
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        (
          K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ∙
          ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ∙
          ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y))))) ◃∎
          =ₛ
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∙
        ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y)))) ◃∎
      K₂-map-∘-coher0 x y = 
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        (
          K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ∙
          ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ∙
          ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y))))) ◃∎
          =ₛ⟨ =ₛ-in
                (ap
                  (λ p →
                    ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ∙
                    ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ∙ p)
                  idp) ⟩
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∙
        ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y)))) ◃∎ ∎ₛ
