{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpPropsMap where

open CohGrp {{...}}

-- various algebraic lemmas on maps of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)) where

  module _
    (map-al : (x y z : G₁) →
      ! (al (map x) (map y) (map z)) ◃∙
      ap (mu (map x)) (map-comp y z) ◃∙
      map-comp x (mu y z) ◃∎
        =ₛ
      ap (λ v → mu v (map z)) (map-comp x y) ◃∙
      map-comp (mu x y) z ◃∙
      ! (ap map (al x y z)) ◃∎)
    (x y z : G₁) where

    abstract
      map-al-rot◃ :
        ! (ap (λ v → mu v (map z)) (map-comp x y)) ◃∙
        ! (al (map x) (map y) (map z)) ◃∎
          =ₛ
        map-comp (mu x y) z ◃∙
        ! (ap map (al x y z)) ◃∙
        ! (map-comp x (mu y z)) ◃∙
        ! (ap (mu (map x)) (map-comp y z)) ◃∎        
      map-al-rot◃ = post-rotate-in (post-rotate-in (pre-rotate'-in (map-al x y z)))

  module _ (map-id : id == map id) where
  
    module _ 
      (map-rho : (x : G₁) →
        ! (map-comp x id) ◃∎
          =ₛ
        ap map (rho x) ◃∙
        ! (rho (map x)) ◃∙
        ap (mu (map x)) map-id ◃∎)
      (x : G₁) where

      abstract
        map-rho-rot◃ :
          ! (ap map (rho x)) ◃∙
          ! (map-comp x id) ◃∙
          ! (ap (mu (map x)) map-id) ◃∙
          rho (map x) ◃∎
            =ₛ
          idp ◃∎
        map-rho-rot◃ =
          ! (ap map (rho x)) ◃∙
          ! (map-comp x id) ◃∙
          ! (ap (mu (map x)) map-id) ◃∙
          rho (map x) ◃∎          
            =ₛ⟨ post-rotate-out (post-rotate'-in (pre-rotate'-in (map-rho x))) ⟩
          []
            =ₛ₁⟨ idp ⟩
          idp ◃∎ ∎ₛ

    module _
      (map-inv : (x : G₁) → inv (map x) == map (inv x))
      (map-rinv : (x : G₁) →
        ap (mu (map x)) (map-inv x) ◃∎
          =ₛ
        ! (rinv (map x)) ◃∙
        map-id ◃∙
        ap map (rinv x) ◃∙
        ! (map-comp x (inv x)) ◃∎)
      (x : G₁) where

      abstract

        map-rinv-rot1◃ :
          ! map-id ◃∎
            =ₛ
          ap map (rinv x) ◃∙
          ! (map-comp x (inv x)) ◃∙
          ! (ap (mu (map x)) (map-inv x)) ◃∙
          ! (rinv (map x)) ◃∎
        map-rinv-rot1◃ = post-rotate-in (post-rotate-in (pre-rotate'-in (pre-rotate-out (map-rinv x))))

        map-rinv-rot2◃ :
          rinv (map x) ◃∙
          ap (mu (map x)) (map-inv x) ◃∙
          map-comp x (inv x) ◃∙
          ! (ap map (rinv x)) ◃∎
            =ₛ
          map-id ◃∎
        map-rinv-rot2◃ = post-rotate'-in (post-rotate-out (pre-rotate-out (map-rinv x)))
