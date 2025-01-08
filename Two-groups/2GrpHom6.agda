{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps2

module 2GrpHom6 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-al : (x y z : G₁) →
  ! (al (map x) (map y) (map z)) ◃∙
  ap (mu (map x)) (map-comp y z) ◃∙
  map-comp x (mu y z) ◃∎
    =ₛ
  ap (λ v → mu v (map z)) (map-comp x y) ◃∙
  map-comp (mu x y) z ◃∙
  ! (ap map (al x y z)) ◃∎)
  (map-inv : (x : G₁) → inv (map x) == map (inv x))
  (map-id : id == map id)
  (map-rinv : (x : G₁) →
    ! (ap (mu (map x)) (map-inv x)) ◃∎
      =ₛ
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! map-id ◃∙
    rinv (map x) ◃∎)
  (map-lam-id :
    ! (lam (map id)) ◃∎
      =ₛ
    ! (ap map (lam id)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) map-id) ◃∎)
  (x : G₁) where

  lam-to-rho0 =
    ! (al (inv (map x)) (map x) id ∙
      ap2 mu (linv (map x)) idp ∙
      lam id) ◃∙
    ap (mu (inv (map x)))
      (rho (map x) ∙
      ! (ap map (rho x)) ∙
      ! (map-comp x id)) ◃∙
    al (inv (map x)) (map x) (map id) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 1 & 1 & ap-∙◃ (mu (inv (map x))) (rho (map x)) _ ⟩
    _
      =ₛ⟨ 0 & 1 & !-∙-seq (al (inv (map x)) (map x) id ◃∙ ap2 mu (linv (map x)) idp ◃∙ lam id ◃∎) ⟩
    _
      =ₛ⟨ 0 & 4 & zz₁-linv-rot (map x) ⟩
    ! (linv (map x)) ◃∙
    ap (mu (inv (map x))) (! (ap map (rho x)) ∙ ! (map-comp x id)) ◃∙
    al (inv (map x)) (map x) (map id) ◃∙
    ap2 (mu) (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 1 & 1 & ap-∙-!-!◃ (mu (inv (map x))) (ap map (rho x)) (map-comp x id) ⟩
    {!!}
    
