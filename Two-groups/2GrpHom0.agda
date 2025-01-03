{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps

module 2GrpHom0 where

open CohGrp {{...}}

module MapInv0 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
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

  linv-to-rinv0 = 
    ! (! (al (inv (map x)) (map x) (inv (map x))) ∙
      ! (ap (mu (inv (map x))) (rinv (map x))) ∙ rho (inv (map x))) ◃∙
    ap (λ z → mu z (inv (map x)))
      (linv (map x) ∙ map-id ∙ ! (ap map (linv x)) ∙ ! (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ⟨ 0 & 1 &
        !-!∙!∙ (al (inv (map x)) (map x) (inv (map x)))
          (ap (mu (inv (map x))) (rinv (map x))) _ ⟩
    _
      =ₛ⟨ 3 & 1 &
        ap-∙∙!! (λ z → mu z (inv (map x))) (linv (map x)) (map-id) (ap map (linv x)) _ ⟩
    ! (rho (inv (map x))) ◃∙
    ap (mu (inv (map x))) (rinv (map x)) ◃∙
    al (inv (map x)) (map x) (inv (map x)) ◃∙
    ap (λ z → mu z (inv (map x))) (linv (map x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv1 =
    ! (rho (inv (map x))) ◃∙
    ap (mu (inv (map x))) (rinv (map x)) ◃∙
    al (inv (map x)) (map x) (inv (map x)) ◃∙
    ap (λ z → mu z (inv (map x))) (linv (map x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ₁⟨ 0 & 4 & ! (zz₂ (map x)) ⟩
    _
      =ₛ⟨ 0 & 1 & hmtpy-nat-!◃ lam (map-inv x) ⟩
    _
      =ₛ⟨ 1 & 1 & map-lam (inv x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (map-comp id (inv x)) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (mu id) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv2 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (map-comp id (inv x)) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (mu id) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ⟨ 2 & 1 & hmtpy-nat-!◃-! (λ z → map-comp z (inv x)) (linv x) ⟩
    _
      =ₛ⟨ 4 & 1 & apCommSq◃ (λ z → ap (mu (map z)) (map-inv x)) (linv x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (mu (map (mu (inv x) x))) (map-inv x)) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (λ z → mu id z) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv3 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (mu (map (mu (inv x) x))) (map-inv x)) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (λ z → mu id z) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ⟨ 4 & 1 & apCommSq◃! (λ z → ap (λ v → mu v z) (map-comp (inv x) x)) (map-inv x) ⟩
    _
      =ₛ⟨ 5 & 1 & apCommSq◃! (λ z → al (map (inv x)) (map x) z) (map-inv x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map (inv x)) (mu (map x) z)) (map-inv x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (λ z → mu id z) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv4 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (map (inv x))) ◃∙
    ! (ap (λ z → mu (map (inv x)) (mu (map x) z)) (map-inv x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (λ z → mu id z) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ⟨ 5 & 1 & map-al-rot2 (inv x) x (inv x) ⟩
    _
      =ₛ⟨ 8 & 1 & hmtpy-nat-!◃-! (λ z → map-comp (inv x) z) (rinv x) ⟩
    _ ∎ₛ

  linv-to-rinv5 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
    ap (λ v → mu v (map (inv x))) (map-comp (inv x) x) ◃∙
    map-comp (mu (inv x) x) (inv x) ◃∙
    ! (ap map (al (inv x) x (inv x))) ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
    ! (map-comp (inv x) id) ◃∙
    ap (λ z → mu (map (inv x)) (map z)) (rinv x) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map (inv x)) (mu (map x) z)) (map-inv x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (mu id) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎
      =ₛ⟨ 9 & 1 & map-rho (inv x) ⟩
    _
      =ₛ⟨ 9 & 1 & ap-seq-=ₛ map (zz₂-rot◃ x) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
    ap (λ v → mu v (map (inv x))) (map-comp (inv x) x) ◃∙
    map-comp (mu (inv x) x) (inv x) ◃∙
    ! (ap map (al (inv x) x (inv x))) ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
    ap map (ap (mu (inv x)) (rinv x)) ◃∙
    ap map (al (inv x) x (inv x)) ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
    ap map (lam (inv x)) ◃∙
    ! (rho (map (inv x))) ◃∙
    ap (mu (map (inv x))) map-id ◃∙
    ap (λ z → mu (map (inv x)) (map z)) (rinv x) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x (inv x))) ◃∙
    ! (ap (λ z → mu (map (inv x)) (mu (map x) z)) (map-inv x)) ◃∙
    al (map (inv x)) (map x) (inv (map x)) ◃∙
    ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
    ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
    ap (mu (map id)) (map-inv x) ◃∙
    ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
    ! (ap (mu id) (map-inv x)) ◃∙
    ap (λ z → mu z (inv (map x))) map-id ◃∙
    ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
    ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
    ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
    rho (map (inv x)) ◃∎ ∎ₛ

  module _ (τ :
    ! (ap (mu (map x)) (map-inv x)) ◃∎
    =ₛ
    map-comp x (inv x) ◃∙
    ! (ap map (rinv x)) ◃∙
    ! map-id ◃∙
    rinv (map x) ◃∎) where

    linv-to-rinv6 =
      ap (λ z → z) (map-inv x) ◃∙
      ! (ap map (lam (inv x))) ◃∙
      ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
      ! (map-comp (mu (inv x) x) (inv x)) ◃∙
      ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
      ap (λ v → mu v (map (inv x))) (map-comp (inv x) x) ◃∙
      map-comp (mu (inv x) x) (inv x) ◃∙
      ! (ap map (al (inv x) x (inv x))) ◃∙
      ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
      ap map (ap (mu (inv x)) (rinv x)) ◃∙
      ap map (al (inv x) x (inv x)) ◃∙
      ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
      ap map (lam (inv x)) ◃∙
      ! (rho (map (inv x))) ◃∙
      ap (mu (map (inv x))) map-id ◃∙
      ap (λ z → mu (map (inv x)) (map z)) (rinv x) ◃∙
      ! (ap (mu (map (inv x))) (map-comp x (inv x))) ◃∙
      ! (ap (λ z → mu (map (inv x)) (mu (map x) z)) (map-inv x)) ◃∙
      al (map (inv x)) (map x) (inv (map x)) ◃∙
      ap (λ v → mu v (inv (map x))) (map-comp (inv x) x) ◃∙
      ap (λ z → mu (map z) (inv (map x))) (linv x) ◃∙
      ap (mu (map id)) (map-inv x) ◃∙
      ! (ap (λ z → mu z (map (inv x))) map-id) ◃∙
      ! (ap (mu id) (map-inv x)) ◃∙
      ap (λ z → mu z (inv (map x))) map-id ◃∙
      ! (ap (λ z → mu z (inv (map x))) (ap map (linv x))) ◃∙
      ! (ap (λ z → mu z (inv (map x))) (map-comp (inv x) x)) ◃∙
      ! (al (map (inv x)) (map x) (inv (map x))) ◃∙
      ! (ap (mu (map (inv x))) (rinv (map x))) ◃∙
      rho (map (inv x)) ◃∎
        =ₛ⟨ 23 & 1 & hmpty-nat-∙◃! (λ z → ap (λ v → mu v z) map-id) (map-inv x) ⟩
      _
        =ₛ₁⟨ 17 & 1 & !-ap-∘ (mu (map (inv x))) (mu (map x)) (map-inv x) ⟩
      _
        =ₛ⟨ 17 & 1 & ap-seq-=ₛ (mu (map (inv x))) τ ⟩
      ap (λ z → z) (map-inv x) ◃∙
      ! (ap map (lam (inv x))) ◃∙
      ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
      ! (map-comp (mu (inv x) x) (inv x)) ◃∙
      ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
      ap (λ v → mu v (map (inv x))) (map-comp (inv x) x) ◃∙
      map-comp (mu (inv x) x) (inv x) ◃∙
      ! (ap map (al (inv x) x (inv x))) ◃∙
      ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
      ap map (ap (mu (inv x)) (rinv x)) ◃∙
      ap map (al (inv x) x (inv x)) ◃∙
      ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
      rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv7 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    ! (map-comp (mu (inv x) x) (inv x)) ◃∙
    ! (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ◃∙
    ap (λ v → mu v (map (inv x))) (map-comp (inv x) x) ◃∙
    map-comp (mu (inv x) x) (inv x) ◃∙
    ! (ap map (al (inv x) x (inv x))) ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
    ap map (ap (mu (inv x)) (rinv x)) ◃∙
    ap map (al (inv x) x (inv x)) ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
      =ₛ₁⟨ 4 & 2 & !-inv-l (ap (λ v → mu v (map (inv x))) (map-comp (inv x) x)) ⟩
    _
      =ₛ₁⟨ 3 & 3 & !-inv-l (map-comp (mu (inv x) x) (inv x)) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    idp ◃∙
    ! (ap map (al (inv x) x (inv x))) ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
    ap map (ap (mu (inv x)) (rinv x)) ◃∙
    ap map (al (inv x) x (inv x)) ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv8 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    idp ◃∙
    ! (ap map (al (inv x) x (inv x))) ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rinv x)) ◃∙
    ap map (ap (mu (inv x)) (rinv x)) ◃∙
    ap map (al (inv x) x (inv x)) ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
      =ₛ₁⟨ 5 & 2 &
        ap2 (λ p₁ p₂ → ! p₁ ∙ p₂) (ap-∘ map (mu (inv x)) (rinv x)) idp ∙
        !-inv-l (ap map (ap (mu (inv x)) (rinv x))) ⟩
    _
      =ₛ₁⟨ 4 & 3 & !-inv-l (ap map (al (inv x) x (inv x))) ⟩
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    idp ◃∙
    idp ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
    rho (map (inv x)) ◃∎ ∎ₛ

  linv-to-rinv9 =
    ap (λ z → z) (map-inv x) ◃∙
    ! (ap map (lam (inv x))) ◃∙
    ! (ap (λ z → map (mu z (inv x))) (linv x)) ◃∙
    idp ◃∙
    idp ◃∙
    ap map (ap (λ z → mu z (inv x)) (linv x)) ◃∙
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
      =ₛ₁⟨ 2 & 4 & 
        ap2 (λ p₁ p₂ → ! p₁ ∙ p₂) (ap-∘ map (λ z → mu z (inv x)) (linv x)) idp ∙
        !-inv-l (ap map (ap (λ z → mu z (inv x)) (linv x))) ⟩
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
    rho (map (inv x)) ◃∎ ∎ₛ
