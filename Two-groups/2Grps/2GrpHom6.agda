{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpProps2
open import 2GrpPropsMap

module 2GrpHom6 where

open CohGrp {{...}}

module MapUnit3 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
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
      =ₛ⟨ 0 & 4 & zz₁-linv-rot1 (map x) ⟩
    ! (linv (map x)) ◃∙
    ap (mu (inv (map x))) (! (ap map (rho x)) ∙ ! (map-comp x id)) ◃∙
    al (inv (map x)) (map x) (map id) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 1 & 1 & hmtpy-nat-∙◃ (λ z → ap (λ v → mu v z) (map-inv x)) (! (ap map (rho x)) ∙ ! (map-comp x id)) ⟩
    _
      =ₛ⟨ 2 & 1 & ap-∙-!-!◃ (mu (map (inv x))) (ap map (rho x)) (map-comp x id) ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    ! (ap (mu (map (inv x))) (ap map (rho x))) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x id)) ◃∙
    ! (ap (λ v → mu v (mu (map x) (map id))) (map-inv x)) ◃∙
    al (inv (map x)) (map x) (map id) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 5 & 1 & apCommSq2◃' (λ z → al z (map x) (map id)) (map-inv x) ⟩
    _
      =ₛ₁⟨ 4 & 2 & !-inv-l (ap (λ v → mu v (mu (map x) (map id))) (map-inv x)) ⟩
    _
      =ₛ₁⟨ 4 & 2 & idp ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    ! (ap (mu (map (inv x))) (ap map (rho x))) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x id)) ◃∙
    al (map (inv x)) (map x) (map id) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎ ∎ₛ

  lam-to-rho1 =
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    ! (ap (mu (map (inv x))) (ap map (rho x))) ◃∙
    ! (ap (mu (map (inv x))) (map-comp x id)) ◃∙
    al (map (inv x)) (map x) (map id) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 3 & 2 & !ₛ (map-al-rot2◃ map map-comp map-al (inv x) x id) ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    ! (ap (mu (map (inv x))) (ap map (rho x))) ◃∙
    map-comp (inv x) (mu x id) ◃∙
    ap map (al (inv x) x id) ◃∙
    ! (map-comp (mu (inv x) x) id) ◃∙
    ! (ap (λ v → mu v (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 5 & 1 & hmtpy-nat-!◃ (λ z → map-comp z id) (linv x) ⟩
    _
      =ₛ⟨ 3 & 1 & apCommSq2◃' (map-comp (inv x)) (rho x) ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    ! (ap (mu (map (inv x))) (ap map (rho x))) ◃∙
    ap (λ z → mu (map (inv x)) (map z)) (rho x) ◃∙
    map-comp (inv x) x ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rho x)) ◃∙
    ap map (al (inv x) x id) ◃∙
    ap (λ z → map (mu z id)) (linv x) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu (map z) (map id)) (linv x)) ◃∙
    ! (ap (λ v → mu v (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ₁⟨ 3 & 1 & ap-∘ (mu (map (inv x))) map (rho x) ⟩
    _
      =ₛ₁⟨ 2 & 2 & !-inv-l (ap (mu (map (inv x))) (ap map (rho x)))  ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rho x)) ◃∙
    ap map (al (inv x) x id) ◃∙
    ap (λ z → map (mu z id)) (linv x) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu (map z) (map id)) (linv x)) ◃∙
    ! (ap (λ v → mu v (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎ ∎ₛ

  lam-to-rho2 =
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap (λ z → map (mu (inv x) z)) (rho x)) ◃∙
    ap map (al (inv x) x id) ◃∙
    ap (λ z → map (mu z id)) (linv x) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu (map z) (map id)) (linv x)) ◃∙
    ! (ap (λ v → mu v (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ₁⟨ 4 & 1 & ap ! (ap-∘ map (mu (inv x)) (rho x)) ⟩
    _
      =ₛ₁⟨ 6 & 1 & ap-∘ map (λ z → mu z id) (linv x) ⟩
    _
      =ₛ₁⟨ 8 & 1 & ap ! (ap-∘ (λ z → mu z (map id)) map (linv x)) ⟩
    ! (linv (map x)) ◃∙
    ap (λ v → mu v (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap map (ap (mu (inv x)) (rho x))) ◃∙
    ap map (al (inv x) x id) ◃∙
    ap map (ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) (ap map (linv x))) ◃∙
    ! (ap (λ v → mu v (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎ ∎ₛ

  lam-to-rho3 =
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap map (ap (mu (inv x)) (rho x))) ◃∙
    ap map (al (inv x) x id) ◃∙
    ap map (ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu (mu z (map x)) (map id)) (map-inv x)) ◃∙
    ap2 mu (linv (map x)) idp ◃∙
    lam (map id) ◃∎
      =ₛ₁⟨ 10 & 1 & ap ! (ap-∘ (λ z → mu z (map id)) (λ z → mu z (map x)) (map-inv x)) ⟩
    _
      =ₛ₁⟨ 5 & 2 & ∙-ap map (al (inv x) x id) (ap (λ z → mu z id) (linv x)) ⟩
    _
      =ₛ₁⟨ 10 & 1 & ap2-idp-r mu (linv (map x)) ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap map (ap (mu (inv x)) (rho x))) ◃∙
    ap map (al (inv x) x id ∙ ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ! (ap (λ z → mu z (map id)) (ap map (linv x))) ◃∙
    ! (ap (λ z → mu z (map id)) (map-comp (inv x) x)) ◃∙
    ! (ap (λ z → mu z (map id)) (ap (λ z → mu z (map x)) (map-inv x))) ◃∙
    ap (λ z → mu z (map id)) (linv (map x)) ◃∙
    lam (map id) ◃∎
      =ₛ⟨ 7 & 3 & !ₛ (ap-∙-!!!◃ (λ z → mu z (map id)) (ap map (linv x)) (map-comp (inv x) x) _) ⟩
    _
      =ₛ⟨ 7 & 2 & 
        ∙-ap◃ (λ z → mu z (map id))
          (! (ap map (linv x)) ∙ ! (map-comp (inv x) x) ∙ ! (ap (λ z → mu z (map x)) (map-inv x)))
          (linv (map x)) ⟩
    ! (linv (map x)) ◃∙
    ap (λ z → mu z (map x)) (map-inv x) ◃∙
    idp ◃∙
    map-comp (inv x) x ◃∙
    ! (ap map (ap (mu (inv x)) (rho x))) ◃∙
    ap map (al (inv x) x id ∙ ap (λ z → mu z id) (linv x)) ◃∙
    ! (map-comp id id) ◃∙
    ap (λ z → mu z (map id))
      ((! (ap map (linv x)) ∙
      ! (map-comp (inv x) x) ∙
      ! (ap (λ z → mu z (map x)) (map-inv x))) ∙
      linv (map x)) ◃∙
    lam (map id) ◃∎ ∎ₛ
