{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpHom6
open import 2GrpHom7

module 2GrpHom8 where

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

  open MapUnit3 map map-comp map-al map-inv map-id x
  open MapUnit4 map map-comp map-inv map-id map-linv map-lam-id x

  abstract
    lam-to-rho :
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
    lam-to-rho =
      lam-to-rho0 ∙ₛ (lam-to-rho1 ∙ₛ (lam-to-rho2 ∙ₛ (lam-to-rho3 ∙ₛ (lam-to-rho4 ∙ₛ lam-to-rho5))))
