{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpPropsMap
open import 2GrpHom3
open import 2GrpHom4

module 2GrpHom5 where

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
  (map-id : id == map id)
  (map-rho-id :
    ! (map-comp id id) ◃∎
      =ₛ
    ap map (rho id) ◃∙
    ! (rho (map id)) ◃∙
    ap (mu (map id)) map-id ◃∎) where

  private
  
    map-inv : (x : G₁) → inv (map x) == map (inv x)
    map-inv x =
      ! (al (inv (map x)) (map x) (inv (map x)) ∙
        ap2 mu (linv (map x)) idp ∙
        lam (inv (map x))) ∙
      ap (mu (inv (map x)))
        (! (rinv (map x)) ∙ map-id ∙ ap map (rinv x) ∙ ! (map-comp x (inv x))) ∙
      al (inv (map x)) (map x) (map (inv x)) ∙
      ap2 mu (linv (map x)) idp ∙
      lam (map (inv x))
      
    map-rinv : (x : G₁) →
      ! (ap (mu (map x)) (map-inv x)) ◃∎
        =ₛ
      map-comp x (inv x) ◃∙
      ! (ap map (rinv x)) ◃∙
      ! map-id ◃∙
      rinv (map x) ◃∎
    map-rinv x = !ₛ (map-inv-map-rinv map map-comp map-id map-inv x (=ₛ-in idp))

  module _ (x : G₁) where

    open MapUnit0 map map-comp map-inv map-id map-al x
    open MapUnit1 map map-comp map-inv map-id map-rinv map-rho-id x

    abstract
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
        rho (map id) ◃∎
          =ₛ
        map-id ◃∎
      rho-to-lam =
        rho-to-lam0 ∙ₛ rho-to-lam1 ∙ₛ rho-to-lam2 ∙ₛ rho-to-lam3 ∙ₛ rho-to-lam4 ∙ₛ rho-to-lam5
