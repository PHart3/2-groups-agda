{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpHom0
open import 2GrpHom1

module 2GrpHom2 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-id : id == map id)
  (map-al-rot2 : (x y z : G₁) →
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
    ap map (rho x) ◃∙
    ! (rho (map x)) ◃∙
    ap (mu (map x)) map-id ◃∎)
  (map-lam : (x : G₁) →
    ! (lam (map x)) ◃∎
      =ₛ
    ! (ap map (lam x)) ◃∙
    ! (map-comp id x) ◃∙
    ! (ap (λ z → mu z (map x)) map-id) ◃∎)
  (x : G₁) where

  open MapInv0 map map-comp map-id map-al-rot2 map-inv map-lam map-rho x
  open MapInv1 map map-comp map-id map-al-rot2 map-inv map-lam map-rho x

  abstract
    -- This theorem is essentially Section 6 of Baez and Lauda.   
    rinv-to-linv :
      ! (ap (mu (map x)) (map-inv x)) ◃∎
        =ₛ
      map-comp x (inv x) ◃∙
      ! (ap map (rinv x)) ◃∙
      ! map-id ◃∙
      rinv (map x) ◃∎
      →
      ! (! (al (inv (map x)) (map x) (inv (map x))) ∙
        ! (ap (mu (inv (map x))) (rinv (map x))) ∙
        rho (inv (map x))) ◃∙
      ap (λ z → mu z (inv (map x)))
        (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)) ◃∙
      ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
      ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
      rho (map (inv x)) ◃∎
        =ₛ
      map-inv x ◃∎
    rinv-to-linv map-rinv =
      rinv-to-linv0 ∙ₛ (rinv-to-linv1 ∙ₛ (rinv-to-linv2 ∙ₛ (rinv-to-linv3 ∙ₛ
      (rinv-to-linv4 ∙ₛ (rinv-to-linv5 ∙ₛ (rinv-to-linv6 map-rinv ∙ₛ
      (rinv-to-linv7 ∙ₛ (rinv-to-linv8 ∙ₛ (rinv-to-linv9 ∙ₛ (rinv-to-linv10 ∙ₛ
      (rinv-to-linv11 ∙ₛ (rinv-to-linv12 ∙ₛ (rinv-to-linv13 ∙ₛ
      rinv-to-linv14)))))))))))))
