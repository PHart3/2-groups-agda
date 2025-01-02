{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpHomEq where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-id : id == map id)
  (map-al-rot2 :
    (x y z : G₁) →
     ! (al (map x) (map y) (map z)) ◃∎
     =ₛ
     ap (λ v → mu v (map z)) (map-comp x y) ◃∙
     map-comp (mu x y) z ◃∙
     ! (ap map (al x y z)) ◃∙
     ! (map-comp x (mu y z)) ◃∙
     ! (ap (mu (map x)) (map-comp y z)) ◃∎)
  (map-inv : (x : G₁) → inv (map x) == map (inv x))
  (map-rho : (x : G₁) →
    ! (map-comp x id) ◃∎
    =ₛ
    ap map (rho x) ◃∙ ! (rho (map x)) ◃∙ ap (mu (map x)) map-id ◃∎)
  (x : G₁) where

  rho-to-lam :
    ! (! (al id (map x) (inv (map x))) ∙
      ! (ap (mu id) (rinv (map x))) ∙
      rho id) ◃∙
    ap (λ z → mu z (inv (map x))) (
      lam (map x) ∙
      ! (ap map (lam x)) ∙
      ! (map-comp id x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    ap (mu (map id)) map-id ◃∙
    map-comp id id ◃∙
    ap map (rho id) ◃∎
      =ₛ
    map-id ◃∎
  rho-to-lam = {!!}
