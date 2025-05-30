{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-comp-aux1
open import KFunctor-comp-aux2
open import KFunctor-comp-aux3

module KFunctor-comp-aux4 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module K₂-map-∘-aux {f₁ : G₁ → G₂} (σ₁ : WkSGrpHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkSGrpHomStr f₂) (x y : G₁) where

    open WkSGrpHomStr

    abstract
      K₂-map-∘-coher :
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        (
          K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) (mu x y) ∙
          ! (K₂-map-β-pts σ₂ (f₁ (mu x y))) ∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ (mu x y))) ∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ (mu x y))) ◃∎
          =ₛ
        ap2 _∙_
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x ∙
            ! (K₂-map-β-pts σ₂ (f₁ x)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x))
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y ∙
            ! (K₂-map-β-pts σ₂ (f₁ y)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ y)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ y)) ◃∙
        ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map σ₂ ∘ K₂-map σ₁)) (loop-comp G₁ x y) ◃∎
      K₂-map-∘-coher =
        K₂-map-∘-coher1 σ₁ σ₂ x y ∙ₛ
          (K₂-map-∘-coher2 σ₁ σ₂ x y ∙ₛ
            K₂-map-∘-coher3 σ₁ σ₂ x y)
