{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps
open import 2GrpPropsMap

module 2GrpHom3 where

open CohGrp {{...}}

module MapUnit0 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-inv : (x : G₁) → inv (map x) == map (inv x))
  (map-id : id == map id)
  (map-al : (x y z : G₁) →
    ! (al (map x) (map y) (map z)) ◃∙
    ap (mu (map x)) (map-comp y z) ◃∙
    map-comp x (mu y z) ◃∎
      =ₛ
    ap (λ v → mu v (map z)) (map-comp x y) ◃∙
    map-comp (mu x y) z ◃∙
    ! (ap map (al x y z)) ◃∎)
  (x : G₁) where

  rho-to-lam0 =
    ! (! (al id (map x) (inv (map x))) ∙
      ! (ap (mu id) (rinv (map x))) ∙
      rho id) ◃∙
    ap (λ z → mu z (inv (map x))) (
      lam (map x) ∙
      ! (ap map (lam x)) ∙
      ! (map-comp id x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 1 & 1 & ap-∙◃ (λ z → mu z (inv (map x))) (lam (map x)) _ ⟩
    ! (! (al id (map x) (inv (map x))) ∙
      ! (ap (mu id) (rinv (map x))) ∙
      rho id) ◃∙
    ap (λ z → mu z (inv (map x))) (lam (map x)) ◃∙
    ap (λ z → mu z (inv (map x))) (! (ap map (lam x)) ∙ ! (map-comp id x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 0 & 2 & !ₛ (zz₁-rinv (map x)) ⟩
    rinv (map x) ◃∙
    ap (λ z → mu z (inv (map x)))
      (! (ap map (lam x)) ∙ ! (map-comp id x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 1 & 1 & hmtpy-nat-∙◃ (λ z → ap (mu z) (map-inv x)) (! (ap map (lam x)) ∙ ! (map-comp id x)) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ap (λ z → mu z (map (inv x)))
      (! (ap map (lam x)) ∙ ! (map-comp id x)) ◃∙
    ! (ap (mu (mu (map id) (map x))) (map-inv x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 2 & 1 & ap-∙-!-!◃ (λ z → mu z (map (inv x))) (ap map (lam x)) (map-comp id x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (map-comp id x)) ◃∙
    ! (ap (mu (mu (map id) (map x))) (map-inv x)) ◃∙
    ! (al (map id) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 5 & 1 & hmtpy-nat-!◃ (al (map id) (map x)) (map-inv x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (map-comp id x)) ◃∙
    ! (ap (mu (mu (map id) (map x))) (map-inv x)) ◃∙
    ap (λ z → mu (mu (map id) (map x)) z) (map-inv x) ◃∙
    ! (al (map id) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 4 & 2 & !-inv-l (ap (mu (mu (map id) (map x))) (map-inv x)) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (map-comp id x)) ◃∙
    idp ◃∙
    ! (al (map id) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 4 & 2 & idp ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (map-comp id x)) ◃∙
    ! (al (map id) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎ ∎ₛ

  rho-to-lam1 =
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (map-comp id x)) ◃∙
    ! (al (map id) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 3 & 2 & map-al-rot1◃ map map-comp map-al id x (inv x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    map-comp (mu id x) (inv x) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (map-comp id (mu x (inv x))) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 5 & 1 & apCommSq2◃! (map-comp id) (rinv x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    map-comp (mu id x) (inv x) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap (λ z → map (mu id z)) (rinv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu (map id) (map z)) (rinv x) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 3 & 1 & apCommSq2◃' (λ z → map-comp z (inv x)) (lam x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ◃∙
    ap (λ z → mu (map z) (map (inv x))) (lam x) ◃∙
    map-comp x (inv x) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (lam x)) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap (λ z → map (mu id z)) (rinv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu (map id) (map z)) (rinv x) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 3 & 1 & ap-∘ (λ z → mu z (map (inv x))) map (lam x) ⟩
    _
      =ₛ₁⟨ 2 & 2 & !-inv-l (ap (λ z → mu z (map (inv x))) (ap map (lam x))) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (lam x)) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap (λ z → map (mu id z)) (rinv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu (map id) (map z)) (rinv x) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎ ∎ₛ

  rho-to-lam2 =
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (lam x)) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap (λ z → map (mu id z)) (rinv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu (map id) (map z)) (rinv x) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 4 & 1 & ap ! (ap-∘ map (λ z → mu z (inv x)) (lam x)) ⟩
    _
      =ₛ₁⟨ 6 & 1 & ap ! (ap-∘ map (mu id) (rinv x)) ⟩
    _
      =ₛ₁⟨ 8 & 1 & ap-∘ (mu (map id)) map (rinv x) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (ap (λ z → mu z (inv x)) (lam x))) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap map (ap (mu id) (rinv x))) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (ap map (rinv x)) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎ ∎ₛ

  rho-to-lam3 =
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (ap (λ z → mu z (inv x)) (lam x))) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap map (ap (mu id) (rinv x))) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (ap map (rinv x)) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map id) (mu (map x) z)) (map-inv x)) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 10 & 1 & ap ! (ap-∘ (mu (map id)) (mu (map x)) (map-inv x)) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (ap (λ z → mu z (inv x)) (lam x))) ◃∙
    ! (ap map (al id x (inv x))) ◃∙
    ! (ap map (ap (mu id) (rinv x))) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (ap map (rinv x)) ◃∙
    ! (ap (mu (map id)) (map-comp x (inv x))) ◃∙
    ! (ap (mu (map id)) (ap (mu (map x)) (map-inv x))) ◃∙
    ! (ap (mu (map id)) (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ⟨ 5 & 2 & !ₛ (ap-∙-!-!◃ map (al id x (inv x)) (ap (mu id) (rinv x))) ⟩
    _
      =ₛ⟨ 8 & 3 & !ₛ (ap-∙-!!!◃ (mu (map id)) (map-comp x (inv x)) (ap (mu (map x)) (map-inv x)) _) ⟩
    _
      =ₛ⟨ 7 & 2 & !ₛ (ap-∙◃ (mu (map id)) (ap map (rinv x)) _) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp x (inv x) ◃∙
    ! (ap map (ap (λ z → mu z (inv x)) (lam x))) ◃∙
    ap map (! (al id x (inv x)) ∙ ! (ap (mu id) (rinv x))) ◃∙
    ! (map-comp id id) ◃∙
    ap (mu (map id)) (
      ap map (rinv x) ∙
      ! (map-comp x (inv x)) ∙
      ! (ap (mu (map x)) (map-inv x)) ∙
      ! (rinv (map x))) ◃∙
    rho (map id) ◃∎
      =ₛ₁⟨ 4 & 1 & !-ap map (ap (λ z → mu z (inv x)) (lam x)) ⟩
    _
      =ₛ⟨ 4 & 2 & !ₛ (ap-∙◃ map (! (ap (λ z → mu z (inv x)) (lam x))) _) ⟩
    rinv (map x) ◃∙
    ap (mu (map x)) (map-inv x) ◃∙
    idp ◃∙
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
      =ₛ₁⟨ 2 & 2 & idp ⟩
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
    rho (map id) ◃∎ ∎ₛ
