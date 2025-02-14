{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-aux3 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) (x y : G₁) where

    open WkMagHomStr

    private
      δ' = ap (λ p → ap (K₂-map σ₂ ∘ K₂-map σ₁) p ∙ idp) (loop-comp G₁ x y)

    abstract
      K₂-map-∘-coher3 :
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
        ! (ap (loop G₃) (map-comp σ₂ (f₁ x) (f₁ y))) ◃∙
        ! (loop-comp G₃ (f₂ (f₁ x)) (f₂ (f₁ y))) ◃∙
        ! (ap2 _∙_ (K₂-map-β-pts σ₂ (f₁ x)) (K₂-map-β-pts σ₂ (f₁ y))) ◃∙
        ! (! (∙-ap (K₂-map σ₂) (loop G₂ (f₁ x)) (loop G₂ (f₁ y)))) ◃∙
        ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₂ (f₁ x) (f₁ y)))) ◃∙
        ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ◃∙
        (! (ap (ap (K₂-map σ₂))
             (! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ∙
             ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ∙
             ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ∙
             loop-comp G₂ (f₁ x) (f₁ y) ∙ ap (loop G₂) (map-comp σ₁ x y))) ∙
           (! (ap (λ z → ap (K₂-map σ₂) (ap (K₂-map σ₁) z)) (loop-comp G₁ x y)) ∙
           (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x ∙ loop G₁ y) ∙
           ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x ∙ loop G₁ y)))) ∙
           ap (λ z → ap (K₂-map σ₂ ∘ K₂-map σ₁) z ∙ idp) (loop-comp G₁ x y))) ◃∎
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
        δ' ◃∎
      K₂-map-∘-coher3 = =ₛ-in {!!}

{-

∙-ap (K₂-map (cohgrphom f₂ ∘2Gσ cohgrphom f₁)) (loop G₁ x)
(loop G₁ y)
∙
ap (ap (K₂-map (cohgrphom f₂ ∘2Gσ cohgrphom f₁)))
(loop-comp G₁ x y)
∙
!
(ap (ap (K₂-map (cohgrphom f₂ ∘2Gσ cohgrphom f₁)))
 (loop-comp G₁ x y))
∙
!
(∙-ap (K₂-map (cohgrphom f₂ ∘2Gσ cohgrphom f₁)) (loop G₁ x)
 (loop G₁ y))
∙
ap2 _∙_ (K₂-map-β-pts (cohgrphom f₂ ∘2Gσ cohgrphom f₁) x)
(K₂-map-β-pts (cohgrphom f₂ ∘2Gσ cohgrphom f₁) y)
∙
loop-comp G₃ ((f₂ ∘ f₁) x) ((f₂ ∘ f₁) y) ∙
ap (loop G₃) (map-comp (cohgrphom f₂ ∘2Gσ cohgrphom f₁) x y) ∙
! (ap (λ z → loop G₃ (f₂ z)) (map-comp σ₁ x y)) ∙
! (ap (loop G₃) (map-comp σ₂ (f₁ x) (f₁ y))) ∙
! (loop-comp G₃ (f₂ (f₁ x)) (f₂ (f₁ y))) ∙
! (ap2 _∙_ (K₂-map-β-pts σ₂ (f₁ x)) (K₂-map-β-pts σ₂ (f₁ y))) ∙
! (! (∙-ap (K₂-map σ₂) (loop G₂ (f₁ x)) (loop G₂ (f₁ y)))) ∙
! (! (ap (ap (K₂-map σ₂)) (loop-comp G₂ (f₁ x) (f₁ y)))) ∙
ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ∙
!
(ap (ap (K₂-map σ₂))
 (! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ∙
  ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ∙
  ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ∙
  loop-comp G₂ (f₁ x) (f₁ y) ∙ ap (loop G₂) (map-comp σ₁ x y)))
∙
! (ap (λ z → ap (K₂-map σ₂) (ap (K₂-map σ₁) z)) (loop-comp G₁ x y))
∙
(∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x ∙ loop G₁ y) ∙
 ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x ∙ loop G₁ y))))
∙ ap (λ z → ap (K₂-map σ₂ ∘ K₂-map σ₁) z ∙ idp) (loop-comp G₁ x y)
==
ap2 _∙_
(K₂-map-β-pts (cohgrphom f₂ ∘2Gσ cohgrphom f₁) x ∙
 ! (K₂-map-β-pts σ₂ (f₁ x)) ∙
 ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ∙
 ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ∙
 ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x))))
(K₂-map-β-pts (cohgrphom f₂ ∘2Gσ cohgrphom f₁) y ∙
 ! (K₂-map-β-pts σ₂ (f₁ y)) ∙
 ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ y)) ∙
 ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ y) ∙
 ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ y))))
∙
∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp (loop G₁ x)
(loop G₁ y)
∙
ap (λ p → ap (K₂-map σ₂ ∘ K₂-map σ₁) p ∙ idp) (loop-comp G₁ x y)

-}
