{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpPropsMap
open import 2GrpHom5
open import 2GrpHom8

module 2GrpHom9 where

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
    map-lam-id :
      ! (lam (map id)) ◃∎
        =ₛ
      ! (ap map (lam id)) ◃∙
      ! (map-comp id id) ◃∙
      ! (ap (λ z → mu z (map id)) map-id) ◃∎
    map-lam-id =
      !ₛ (map-id-map-lam map map-comp map-id id
        (!ₛ (rho-to-lam map map-comp map-al 
          map-id map-rho-id id)))

  -- This lets us eliminate the unit iso from the definition of 2-group morphism.
  abstract
    rhoid-to-rho : (x : G₁) → 
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
        =ₛ
      map-id ◃∎
    rhoid-to-rho x =
      lam-to-rho map map-comp map-al
        (λ v → 
          ! (! (al (inv (map v)) (map v) (inv (map v))) ∙
            ! (ap (mu (inv (map v))) (rinv (map v))) ∙
            rho (inv (map v))) ∙
          ap (λ z → mu z (inv (map v)))
            (linv (map v) ∙ map-id ∙ ! (ap map (linv v)) ∙ ! (map-comp (inv v) v)) ∙
          ! (al (map (inv v)) (map v) (inv (map v))) ∙
          ! (ap (mu (map (inv v))) (rinv (map v))) ∙
          rho (map (inv v)))
        map-id
        (λ u → !ₛ (map-inv-map-linv map map-comp map-id
          (λ v → 
            ! (! (al (inv (map v)) (map v) (inv (map v))) ∙
              ! (ap (mu (inv (map v))) (rinv (map v))) ∙
              rho (inv (map v))) ∙
            ap (λ z → mu z (inv (map v)))
              (linv (map v) ∙ map-id ∙ ! (ap map (linv v)) ∙ ! (map-comp (inv v) v)) ∙
            ! (al (map (inv v)) (map v) (inv (map v))) ∙
            ! (ap (mu (map (inv v))) (rinv (map v))) ∙
            rho (map (inv v)))
          u (=ₛ-in idp)))
        map-lam-id
        x
