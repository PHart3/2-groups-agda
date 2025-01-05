{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpHom0
open import 2GrpHom1

module 2GrpHom2 where

open CohGrp {{...}}

module MapInv2 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
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

  open MapInv0 map map-comp map-id map-al-rot2 map-inv map-lam map-rho x
  open MapInv1 map map-comp map-id map-al-rot2 map-inv map-lam map-rho x

  abstract
    -- This theorem is essentially Section 6 of Baez and Lauda.   
    linv-to-rinv :
      ! (ap (mu (map x)) (map-inv x))
        ==
      map-comp x (inv x) ∙
      ! (ap map (rinv x)) ∙
      ! map-id ∙
      rinv (map x)
      →
      ! (! (al (inv (map x)) (map x) (inv (map x))) ∙
      ! (ap (mu (inv (map x))) (rinv (map x))) ∙ rho (inv (map x))) ◃∙
      ap (λ z → mu z (inv (map x)))
        (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)) ◃∙
      ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
      ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
      rho (map (inv x)) ◃∎
        =ₛ
      map-inv x ◃∎
    linv-to-rinv τ =
      linv-to-rinv0 ∙ₛ (linv-to-rinv1 ∙ₛ (linv-to-rinv2 ∙ₛ (linv-to-rinv3 ∙ₛ
      (linv-to-rinv4 ∙ₛ (linv-to-rinv5 ∙ₛ (linv-to-rinv6 (=ₛ-in τ) ∙ₛ
      (linv-to-rinv7 ∙ₛ (linv-to-rinv8 ∙ₛ (linv-to-rinv9 ∙ₛ (linv-to-rinv10 ∙ₛ
      (linv-to-rinv11 ∙ₛ (linv-to-rinv12 ∙ₛ (linv-to-rinv13 ∙ₛ
      linv-to-rinv14)))))))))))))
