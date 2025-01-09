{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import 2Grp

module 2GrpPropsMap2 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} (map : G₁ → G₂) where

  -- various algebraic lemmas on maps of 2-groups
  module _ (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
    (map-id : id == map id) where

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

      -- properties about map-linv

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

  -- equality of 2-group maps
  open CohGrpHomStrFull {{...}}
  module _
    {{ρ : CohGrpHomStrFull map}}
    (map-id₀ : id == map id)
    (map-rho₀ : (x : G₁) →
      ! (map-comp x id)
        ==
      ap map (rho x) ∙
      ! (rho (map x)) ∙
      ap (mu (map x)) map-id₀)
    (map-lam₀ : (x : G₁) →
      ! (lam (map x))
        ==
      ! (ap map (lam x)) ∙
      ! (map-comp id x) ∙
      ! (ap (λ z → mu z (map x)) map-id₀))
    (map-inv₀ : (x : G₁) → inv (map x) == map (inv x))
    (map-rinv₀ : (x : G₁) →
      ! (ap (mu (map x)) (map-inv₀ x))
        ==
      map-comp x (inv x) ∙
      ! (ap map (rinv x)) ∙
      ! map-id₀ ∙
      rinv (map x))
    (map-linv₀ : (x : G₁) → 
      ! (ap (λ z → mu z (map x)) (map-inv₀ x))
        ==
      map-comp (inv x) x ∙
      ap map (linv x) ∙
      ! map-id₀ ∙
      ! (linv (map x))) where
      
    2grphomfulleq :
      map-id₀ == map-id
      → map-inv₀ == map-inv
      → ρ == cohgrphomstrfull map-comp map-al map-id₀ map-rho₀ map-lam₀ map-inv₀ map-rinv₀ map-linv₀
    2grphomfulleq idp idp = 
      ap4 (λ c₁ c₂ c₃ c₄ → cohgrphomstrfull map-comp map-al map-id c₁ c₂ map-inv c₃ c₄)
        (λ= (λ x → prop-has-all-paths (map-rho x) (map-rho₀ x)))
        (λ= (λ x → prop-has-all-paths (map-lam x) (map-lam₀ x)))
        (λ= (λ x → prop-has-all-paths (map-rinv x) (map-rinv₀ x)))
        (λ= (λ x → prop-has-all-paths (map-linv x) (map-linv₀ x)))

