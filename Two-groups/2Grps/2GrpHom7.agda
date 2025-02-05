{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps2
open import 2GrpPropsMap2

module 2GrpHom7 where

open CohGrp {{...}}

module MapUnit4 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-inv : (x : G₁) → inv (map x) == map (inv x))
  (map-id : id == map id)
  (map-linv : (x : G₁) →
    ! (ap (λ z → mu z (map x)) (map-inv x)) ◃∎
      =ₛ
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    ! map-id ◃∙
    ! (linv (map x)) ◃∎)
  (map-lam-id :
    ! (lam (map id)) ◃∎
      =ₛ
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) map-id) ◃∎)
  (x : G₁) where

  lam-to-rho4 =
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap map (ap (mu (inv x)) (rho x))) ◃∙
    ap map (al (inv x) x id ∙ ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu z (map id))
      ((! (ap map (linv x)) ∙
      ! (map-comp (inv x) x) ∙
      ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
      linv (map x)) ◃∙
    lam (map id) ◃∎
      =ₛ₁⟨ 4 & 1 & !-ap map (ap (mu (inv x)) (rho x)) ⟩
    _
      =ₛ₁⟨ 4 & 2 & ∙-ap map (! (ap (mu (inv x)) (rho x))) (al (inv x) x id ∙ ap (λ z → mu z id) (linv x)) ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (
      ! (ap (mu (inv x)) (rho x)) ∙
      al (inv x) x id ∙
      ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu z (map id)) (
      (! (ap map (linv x)) ∙
      ! (map-comp (inv x) x) ∙
      ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
      linv (map x)) ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 4 & 1 & ∙-ap-seq-=ₛ map (!ₛ (zz₁-linv-rot2 x)) ⟩
    _
      =ₛ₁⟨ 5 & 1 & ap-! map (lam id) ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu z (map id)) (
      (! (ap map (linv x)) ∙
      ! (map-comp (inv x) x) ∙
      ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
      linv (map x)) ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 7 & 1 & ap-seq-=ₛ (λ z → mu z (map id)) (map-linv-rot1◃ map map-comp map-id map-inv map-linv x) ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu z (map id)) (! map-id) ◃∙
    lam (map id) ◃∎
      =ₛ₁⟨ 7 & 1 & ap-! (λ z → mu z (map id)) map-id ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) map-id) ◃∙
    lam (map id) ◃∎ ∎ₛ

  lam-to-rho5 =
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) map-id) ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 5 & 4 & map-lam-rot1◃ map map-comp map-id id map-lam-id ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ap map (linv x) ◃∙
    idp ◃∎
      =ₛ₁⟨ 0 & 5 & ! (=ₛ-out (map-linv-rot2◃ map map-comp map-id map-inv map-linv x)) ⟩
    map-id ◃∙
    idp ◃∎
      =ₛ₁⟨ ∙-unit-r map-id ⟩
    map-id ◃∎ ∎ₛ
