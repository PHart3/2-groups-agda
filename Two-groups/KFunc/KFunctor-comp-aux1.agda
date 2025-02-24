{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-aux1 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) (x y : G₁) where

    open WkMagHomStr

    abstract
      K₂-map-∘-coher1 :
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        (
          K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ∙
          ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y))) ◃∎
          =ₛ
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        ! (ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y) ◃∙
        loop-comp G₃ ((f₂ ∘ f₁) x) ((f₂ ∘ f₁) y) ◃∙
        ap (loop G₃) (map-comp (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x y) ◃∙
        ! (ap (λ z → loop G₃ (f₂ z)) (map-comp σ₁ x y)) ◃∙
        ! (K₂-map-β-pts σ₂ (mu (f₁ x) (f₁ y))) ◃∙
        ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∎
      K₂-map-∘-coher1 =
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        (
          K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ∙
          ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y))) ◃∎
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
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∎
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
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∎
          =ₛ⟨ 7 & 1 & apCommSq2◃! (K₂-map-β-pts σ₂) (map-comp σ₁ x y) ⟩
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        ! (ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y) ◃∙
        loop-comp G₃ ((f₂ ∘ f₁) x) ((f₂ ∘ f₁) y) ◃∙
        ap (loop G₃) (map-comp (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x y) ◃∙
        ! (ap (λ z → loop G₃ (f₂ z)) (map-comp σ₁ x y)) ◃∙
        ! (K₂-map-β-pts σ₂ (mu (f₁ x) (f₁ y))) ◃∙
        ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y)) ◃∎ ∎ₛ
