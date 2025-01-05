{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpPropsMap where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) (map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y))
  (map-al : (x y z : G₁) →
    ! (al (map x) (map y) (map z)) ◃∙
    ap (mu (map x)) (map-comp y z) ◃∙
    map-comp x (mu y z) ◃∎
     =ₛ
    ap (λ v → mu v (map z)) (map-comp x y) ◃∙
    map-comp (mu x y) z ◃∙
    ! (ap map (al x y z)) ◃∎) where

  module _ (x y z : G₁) where

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


{-
    abstract
      map-comp-eq :
        map-comp y z ◃∎
          =ₛ
        ! (lam (mu (map y) (map z))) ◃∙
        ! (ap (λ v → mu v (mu (map y) (map z))) (linv (map x))) ◃∙
        ! (al (inv (map x)) (map x) (mu (map y) (map z))) ◃∙
        ap (mu (inv (map x))) (al (map x) (map y) (map z)) ◃∙
        ap (mu (inv (map x))) (ap (λ v → mu v (map z)) (map-comp x y)) ◃∙
        ap (mu (inv (map x))) (map-comp (mu x y) z) ◃∙
        ap (mu (inv (map x))) (! (ap map (al x y z))) ◃∙
        ap (mu (inv (map x))) (! (map-comp x (mu y z))) ◃∙
        al (inv (map x)) (map x) (map (mu y z)) ◃∙
        ap (λ v → mu v (map (mu y z))) (linv (map x)) ◃∙
        lam (map (mu y z)) ◃∎
      map-comp-eq = 
        map-comp y z ◃∎
          =ₛ₁⟨ ! (<–-inv-l (ap-equiv (mu (map x) , mu-pre-iso (map x)) _ _) (map-comp y z)) ⟩
        _
          =ₛ⟨ =ₛ-in
                (ap (<– (ap-equiv (mu (map x) , mu-pre-iso (map x))
                  (mu (map y) (map z))
                  (map (mu y z))))
                (=ₛ-out map-al-rot◃)) ⟩
        ! (al (inv (map x)) (map x) (mu (map y) (map z)) ∙
          ap2 mu (linv (map x)) idp ∙
          lam (mu (map y) (map z))) ◃∙
        ap (mu (inv (map x))) (
          al (map x) (map y) (map z) ∙
          ap (λ v → mu v (map z)) (map-comp x y) ∙
          map-comp (mu x y) z ∙
          ! (ap map (al x y z)) ∙
          ! (map-comp x (mu y z))) ◃∙
        al (inv (map x)) (map x) (map (mu y z)) ◃∙
        ap2 mu (linv (map x)) idp ◃∙
        lam (map (mu y z)) ◃∎
          =ₛ⟨ 0 & 1 &
            !-∙-seq (
              al (inv (map x)) (map x) (mu (map y) (map z)) ◃∙
              ap2 mu (linv (map x)) idp ◃∙
              lam (mu (map y) (map z)) ◃∎) ⟩
        _
          =ₛ₁⟨ 1 & 1 & ap ! (ap2-idp-r mu (linv (map x))) ⟩
        _
          =ₛ₁⟨ 5 & 1 & ap2-idp-r mu (linv (map x)) ⟩
        _
          =ₛ⟨ 3 & 1 & 
            ap-seq-∙ (mu (inv (map x))) (
              al (map x) (map y) (map z) ◃∙
              ap (λ v → mu v (map z)) (map-comp x y) ◃∙
              map-comp (mu x y) z ◃∙
              ! (ap map (al x y z)) ◃∙
              ! (map-comp x (mu y z)) ◃∎) ⟩
        ! (lam (mu (map y) (map z))) ◃∙
        ! (ap (λ v → mu v (mu (map y) (map z))) (linv (map x))) ◃∙
        ! (al (inv (map x)) (map x) (mu (map y) (map z))) ◃∙
        ap (mu (inv (map x))) (al (map x) (map y) (map z)) ◃∙
        ap (mu (inv (map x))) (ap (λ v → mu v (map z)) (map-comp x y)) ◃∙
        ap (mu (inv (map x))) (map-comp (mu x y) z) ◃∙
        ap (mu (inv (map x))) (! (ap map (al x y z))) ◃∙
        ap (mu (inv (map x))) (! (map-comp x (mu y z))) ◃∙
        al (inv (map x)) (map x) (map (mu y z)) ◃∙
        ap (λ v → mu v (map (mu y z))) (linv (map x)) ◃∙
        lam (map (mu y z)) ◃∎ ∎ₛ

  module _ (map-id : id == map id) (x : G₁) where

    map-comp-id :
      map-comp id x ◃∎
        =ₛ
      ! (ap (λ z → mu z (map x)) map-id) ◃∙
      lam (map x) ◃∙
      ! (ap map (lam x)) ◃∎
    map-comp-id = {!!}

-}
