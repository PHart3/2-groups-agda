{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import 2Magma
open import 2Grp

module 2GrpSIP-aux where

module _ {i} (G₁ : Type i) (η₁ : CohGrp G₁) where

  open CohGrp η₁

  2grphomf-Σ-contr :
    [ ( ( G₂ , _ ) , ( map , _ ) ) ∈ Σ (1 -Type i) (λ ( G₂ , _ ) → G₁ ≃ G₂) ] ×
      [ ( mu₂ , map-comp ) ∈ Σ (G₂ → G₂ → G₂) (λ mu₂ → (x y : G₁) → mu₂ (map x) (map y) == map (mu x y)) ] ×
        [ ( id₂ , map-id ) ∈ Σ G₂ (λ id₂ → id₂ == map id) ] ×
          [ ( lam₂ , map-lam ) ∈
            Σ ((x : G₂) → mu₂ id₂ x == x)
              (λ lam₂ →
                (x : G₁) → ! (lam₂ (map x)) == ! (ap map (lam x)) ∙ ! (map-comp id x) ∙ ! (ap (λ z → mu₂ z (map x)) map-id)) ] ×
            [ ( rho₂ , map-rho ) ∈
              Σ ((x : G₂) → mu₂ x id₂ == x)
                (λ rho₂ →
                  (x : G₁) → ! (map-comp x id) == ap map (rho x) ∙ ! (rho₂ (map x)) ∙ ap (mu₂ (map x)) map-id) ] ×
              [ ( al₂ , map-al ) ∈
                Σ ((x y z : G₂) → mu₂ x (mu₂ y z) == mu₂ (mu₂ x y) z)
                  (λ al₂ →
                    (x y z : G₁) →
                      ! (al₂ (map x) (map y) (map z)) ∙ ap (mu₂ (map x)) (map-comp y z) ∙ map-comp x (mu y z)
                        ==
                      ap (λ v → mu₂ v (map z)) (map-comp x y) ∙ map-comp (mu x y) z ∙ ! (ap map (al x y z))) ] ×
                [ tr₂ ∈ ((x y : G₂) → ap (λ z → mu₂ z y) (rho₂ x) == ! (al₂ x id₂ y) ∙ ap (mu₂ x) (lam₂ y)) ] ×
                  [ pent₂ ∈ ((w x y z : G₂) →
                      al₂ w x (mu₂ y z) ∙ al₂ (mu₂ w x) y z
                        ==
                      ap (mu₂ w) (al₂ x y z) ∙ al₂ w (mu₂ x y) z ∙ ap (λ v → mu₂ v z) (al₂ w x y)) ] ×
                    [ ( inv₂ , map-inv ) ∈ Σ (G₂ → G₂) (λ inv₂ → (x : G₁) → inv₂ (map x) == map (inv x)) ] ×
                      [ ( linv₂ , map-linv ) ∈
                        Σ ((x : G₂) → mu₂ (inv₂ x) x == id₂)
                          (λ linv₂ →
                            (x : G₁) →
                              ! (ap (λ z → mu₂ z (map x)) (map-inv x))
                                ==
                              map-comp (inv x) x ∙ ap map (linv x) ∙ ! map-id ∙ ! (linv₂ (map x))) ] ×
                        [ ( rinv₂ , map-rinv ) ∈
                          Σ ((x : G₂) → id₂ == mu₂ x (inv₂ x))
                            (λ rinv₂ →
                              (x : G₁) →
                                ! (ap (mu₂ (map x)) (map-inv x))
                                  ==
                                map-comp x (inv x) ∙ ! (ap map (rinv x)) ∙ ! map-id ∙ rinv₂ (map x)) ] ×
                          [ zz₁₂ ∈
                              ((x : G₂) →
                                lam₂ x
                                  ==
                                ap (λ z → mu₂ z x) (rinv₂ x) ∙ ! (al₂ x (inv₂ x) x) ∙ ap (mu₂ x) (linv₂ x) ∙ rho₂ x) ] ×
                            ((x : G₂) →
                              ! (lam₂ (inv₂ x))
                                ==
                              ! (rho₂ (inv₂ x)) ∙
                              ap (mu₂ (inv₂ x)) (rinv₂ x) ∙
                              al₂ (inv₂ x) x (inv₂ x) ∙
                              ap (λ z → mu₂ z (inv₂ x)) (linv₂ x))
      ≃
    Unit
  2grphomf-Σ-contr = {!!}
