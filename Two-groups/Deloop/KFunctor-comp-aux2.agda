{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

-- K₂-map respects composition

module KFunctor-comp-aux2 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) (x y : G₁) where

    open WkMag hiding (mu)
    open WkMagHomStr

    abstract
      K₂-map-∘-coher1 :
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∙
        ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y)))) ◃∎
          =ₛ
        ap2 _∙_
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x ∙
            ! (K₂-map-β-pts σ₂ (f₁ x)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ∙
            ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x))))
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y ∙
            ! (K₂-map-β-pts σ₂ (f₁ y)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ y)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ y) ∙
            ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ y)))) ◃∙
        ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp (loop G₁ x) (loop G₁ y) ◃∙
        ap (λ p → ap (K₂-map σ₂ ∘ K₂-map σ₁) p ∙ idp) (loop-comp G₁ x y) ◃∎
      K₂-map-∘-coher1 = 
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∙
        ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y)))) ◃∎
          =ₛ⟨ 2 & 1 & K₂-map-β-comp (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x y ⟩
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        ! (ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y) ◃∙
        loop-comp G₃ ((f₂ ∘ f₁) x) ((f₂ ∘ f₁) y) ◃∙
        ap (loop G₃) (map-comp (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x y) ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∙
        ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ (mu x y)))) ◃∎
          =ₛ⟨ 7 & 1 & {!!} ⟩
        {!!}
