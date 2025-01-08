
{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpPropsMap2 where

open CohGrp {{...}}

-- various algebraic lemmas on maps of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂)
  (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)) where

  module _ (map-id : id == map id) where

    module _ (x : G₁) where 

      -- properties about map-lam

      module _ 
        (map-lam :
          ! (lam (map x)) ◃∎
            =ₛ
          ! (ap map (lam x)) ◃∙
          ! (map-comp id x) ◃∙
          ! (ap (λ z → mu z (map x)) map-id) ◃∎) where

        abstract
          map-lam-rot1◃ :
            ! (ap map (lam x)) ◃∙
            ! (map-comp id x) ◃∙
            ! (ap (λ z → mu z (map x)) map-id) ◃∙
            lam (map x) ◃∎
              =ₛ
            idp ◃∎
          map-lam-rot1◃ = 
            ! (ap map (lam x)) ◃∙
            ! (map-comp id x) ◃∙
            ! (ap (λ z → mu z (map x)) map-id) ◃∙
            lam (map x) ◃∎
              =ₛ⟨ post-rotate-out (!ₛ map-lam) ⟩
            []
              =ₛ₁⟨ idp ⟩
            idp ◃∎ ∎ₛ

    module _ (map-inv : (x : G₁) → inv (map x) == map (inv x))  where

      -- properties about map-rinv

      module _
        (map-linv : (x : G₁) →
          ! (ap (λ z → mu z (map x)) (map-inv x)) ◃∎
            =ₛ
          map-comp (inv x) x ◃∙
          ap map (linv x) ◃∙
          ! map-id ◃∙
          ! (linv (map x)) ◃∎)
        (x : G₁) where

        abstract
        
          map-linv-rot1◃ :
            ((! (ap map (linv x)) ∙
              ! (map-comp (inv x) x) ∙  
              ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
            linv (map x)) ◃∎
              =ₛ
            ! map-id ◃∎
          map-linv-rot1◃ = 
            ((! (ap map (linv x)) ∙
              ! (map-comp (inv x) x) ∙  
              ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
            linv (map x)) ◃∎
              =ₛ⟨ =ₛ-in idp ⟩
            (! (ap map (linv x)) ∙
              ! (map-comp (inv x) x) ∙  
              ! (ap (λ z → mu z (map x)) (map-inv x))) ◃∙
            linv (map x) ◃∎
              =ₑ⟨ 0 & 1 & (! (ap map (linv x)) ◃∙ ! (map-comp (inv x) x) ◃∙ ! (ap (λ z → mu z (map x)) (map-inv x)) ◃∎)
                % =ₛ-in idp ⟩
            ! (ap map (linv x)) ◃∙
            ! (map-comp (inv x) x) ◃∙
            ! (ap (λ z → mu z (map x)) (map-inv x)) ◃∙
            linv (map x) ◃∎
              =ₛ⟨ pre-rotate'-in (pre-rotate'-in (post-rotate-out (map-linv x))) ⟩
            ! map-id ◃∎ ∎ₛ

          map-linv-rot2◃ :
            map-id ◃∎
              =ₛ
            ! (linv (map x)) ◃∙
            ap (λ z → mu z (map x)) (map-inv x) ◃∙
            map-comp (inv x) x ◃∙
            ap map (linv x) ◃∎
          map-linv-rot2◃ = pre-rotate-in (pre-rotate'-out (post-rotate-out (post-rotate-out (map-linv x))))
