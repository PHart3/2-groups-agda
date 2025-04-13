{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps
open import 2GrpPropsMap

module 2GrpHom4 where

open CohGrp {{...}}

module MapUnit1 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-inv : (x : G₁) → inv (map x) == map (inv x))
  (map-id : id == map id)
  (map-rinv : (x : G₁) →
    ! (ap (mu (map x)) (map-inv x)) ◃∎
      =ₛ
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! map-id ◃∙
    rinv (map x) ◃∎)
  (map-rho-id :
    ! (map-comp id id) ◃∎
      =ₛ
    ap map (rho id) ◃∙
    ! (rho (map id)) ◃∙
    ap (mu (map id)) map-id ◃∎)
  (x : G₁) where

  rho-to-lam4 = 
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ap map (
      ! (ap (λ z → mu z (inv x)) (lam x)) ∙
      ! (al id x (inv x)) ∙
      ! (ap (mu id) (rinv x))) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (
      ap map (rinv x) ∙
      ! (map-comp x (inv x)) ∙
      ! (ap (mu (map x)) (map-inv x)) ∙
      ! (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 3 & 1 & ∙-ap-seq-=ₛ map (zz₁-rinv-rot x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ap map (! (rinv x)) ◃∙
    ap map (! (rho id)) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (
      ap map (rinv x) ∙
      ! (map-comp x (inv x)) ∙
      ! (ap (mu (map x)) (map-inv x)) ∙
      ! (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 3 & 2 & !-!-ap-∙◃ map (rinv x) (rho id) ⟩
    _
      =ₛ⟨ 6 & 1 &
        ∙-ap-seq-=ₛ (mu (map id))
          (map-rinv-rot1◃ map map-comp map-id map-inv map-rinv x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! (ap map (rho id)) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (! map-id) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 6 & 1 & ap-! (mu (map id)) (map-id) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! (ap map (rho id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (mu (map id)) map-id) ◃∙
    rho (map id) ◃∎ ∎ₛ

  rho-to-lam5 =
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! (ap map (rho id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (mu (map id)) map-id) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 4 & 4 & map-rho-rot1◃ map map-comp map-id id map-rho-id ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    idp ◃∎
      =ₛ⟨ 0 & 4 & !ₛ (map-rinv-rot2◃ map map-comp map-id map-inv map-rinv x) ⟩
    map-id ◃∙ idp ◃∎
      =ₛ₁⟨ ∙-unit-r (map-id) ⟩
    map-id ◃∎ ∎ₛ
