{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpHom1 where

open CohGrp {{...}}

module MapInv1 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
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
  (map-lam : (x : G₁) →
    ! (lam (map x)) ◃∎
    =ₛ
    ! (ap map (lam x)) ◃∙ ! (map-comp id x) ◃∙ ! (ap (λ z → mu z (map x)) map-id) ◃∎)
  (map-rho : (x : G₁) →
    ! (map-comp x id) ◃∎
    =ₛ
    ap map (rho x) ◃∙ ! (rho (map x)) ◃∙ ap (mu (map x)) map-id ◃∎)
  (x : G₁) where

  rinv-to-linv10 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    idp ◃∙
    ap map (lam (inv x)) ◃∙
    ! (rho (map (inv x))) ◃∙
    ap (mu (map (inv x))) map-id ◃∙
    ap (λ z → mu (map (inv x)) (map z)) (rinv x) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x (inv x))) ◃∙
    ap (mu (map (inv x))) (map-comp x (inv x)) ◃∙
    ap (mu (map (inv x))) (! (ap map (rinv x))) ◃∙
    ap (mu (map (inv x))) (! map-id) ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ap (λ v → mu v (map (inv x))) map-id ◃∙
    ! (ap (λ z → mu (map id) z) (map-inv x)) ◃∙
    ! (ap (λ v → mu v (inv (map x))) map-id) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 1 & 3 & !-inv-l (ap map (lam (inv x))) ⟩
    _
      =ₛ₁⟨ 5 & 2 & !-inv-l (ap (mu (map (inv x))) (map-comp x (inv x))) ⟩
    _
      =ₛ₁⟨ 4 & 3 & ∘-ap-!-inv-r (mu (map (inv x))) map (rinv x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    ap (mu (map (inv x))) map-id ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (! map-id) ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ap (λ v → mu v (map (inv x))) map-id ◃∙
    ! (ap (λ z → mu (map id) z) (map-inv x)) ◃∙
    ! (ap (λ v → mu v (inv (map x))) map-id) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  rinv-to-linv11 =
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    ap (mu (map (inv x))) map-id ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (! map-id) ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ap (λ v → mu v (map (inv x))) map-id ◃∙
    ! (ap (λ z → mu (map id) z) (map-inv x)) ◃∙
    ! (ap (λ v → mu v (inv (map x))) map-id) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 3 & 3 & ap-!-inv (mu (map (inv x))) map-id ⟩
    _  
      =ₛ₁⟨ 9 & 2 & !-inv-l (ap (λ z → (mu z (map (inv x)))) map-id) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    idp ◃∙
    ! (ap (λ z → mu (map id) z) (map-inv x)) ◃∙
    ! (ap (λ v → mu v (inv (map x))) map-id) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  rinv-to-linv12 =
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    idp ◃∙
    ! (ap (λ z → mu (map id) z) (map-inv x)) ◃∙
    ! (ap (λ v → mu v (inv (map x))) map-id) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 8 & 3 & !-inv-r (ap (mu (map id)) (map-inv x)) ⟩
    _
      =ₛ₁⟨ 9 & 2 & !-inv-l (ap (λ z → mu z (inv (map x))) map-id) ⟩
    _
      =ₛ₁⟨ 7 & 4 & ∘-!-ap-inv-r (λ z → mu z (inv (map x))) map (linv x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    idp ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  rinv-to-linv13 =
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    ap (mu (map (inv x))) (rinv (map x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    idp ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 6 & 3 & !-inv-r (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ⟩
    _
      =ₛ₁⟨ 5 & 3 & !-inv-r (al (map (inv x)) (map x) (inv (map x))) ⟩
    _
      =ₛ₁⟨ 4 & 3 & !-inv-r (ap (mu (map (inv x))) (rinv (map x))) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    idp ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  rinv-to-linv14 =
    ap (λ z → z) (map-inv x) ◃∙
    idp ◃∙
    ! (rho (map (inv x))) ◃∙
    idp ◃∙
    idp ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 1 & 5 & !-inv-l (rho (map (inv x))) ⟩
    ap (λ z → z) (map-inv x) ◃∙ idp ◃∎
      =ₛ₁⟨ ∙-unit-r (ap (λ z → z) (map-inv x)) ∙ ap-idf (map-inv x) ⟩
    map-inv x ◃∎ ∎ₛ
