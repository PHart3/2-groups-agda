{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.FTID
open import lib.Funext2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.Unit
open import 2Magma
open import 2Grp

module 2GrpSIP-aux where

module _ {i} (G₁ : Type i) (η₁ : CohGrp G₁) where

  open CohGrp η₁

  -- big nested Σ-type to be contracted
  private
    Θ =
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
                        [ tr₂ ∈ ((x y : G₂) → ap (λ z → mu₂ z y) (rho₂ x) == ! (al₂ x id₂ y) ∙ ap (mu₂ x) (lam₂ y)) ] ×
                          [ pent₂ ∈ ((w x y z : G₂) →
                              al₂ w x (mu₂ y z) ∙ al₂ (mu₂ w x) y z
                                ==
                              ap (mu₂ w) (al₂ x y z) ∙ al₂ w (mu₂ x y) z ∙ ap (λ v → mu₂ v z) (al₂ w x y)) ] ×
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

  open import 2GrpSIP-aux2 G₁ η₁

  2grphomf-Σ-contr0 =
    Θ
      ≃⟨  Σ-contr-red {A = Σ (1 -Type i) (λ (G₂ , _) → G₁ ≃ G₂)} (nType=-contr (G₁ , 1trunc)) ⟩
    [ ( mu₂ , map-comp ) ∈ Σ (G₁ → G₁ → G₁) (λ mu₂ → (x y : G₁) → mu₂ x y == mu x y) ] ×
      [ ( id₂ , map-id ) ∈ Σ G₁ (λ id₂ → id₂ == id) ] ×
        [ ( lam₂ , map-lam ) ∈
          Σ ((x : G₁) → mu₂ id₂ x == x)
            (λ lam₂ →
              (x : G₁) → ! (lam₂ x) == ! (ap (λ v → v) (lam x)) ∙ ! (map-comp id x) ∙ ! (ap (λ z → mu₂ z x) map-id)) ] ×
          [ ( rho₂ , map-rho ) ∈
            Σ ((x : G₁) → mu₂ x id₂ == x)
              (λ rho₂ →
                (x : G₁) → ! (map-comp x id) == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ ap (mu₂ x) map-id) ] ×
            [ ( al₂ , map-al ) ∈
              Σ ((x y z : G₁) → mu₂ x (mu₂ y z) == mu₂ (mu₂ x y) z)
                (λ al₂ →
                  (x y z : G₁) →
                    ! (al₂ x y z) ∙ ap (mu₂ x) (map-comp y z) ∙ map-comp x (mu y z)
                      ==
                    ap (λ v → mu₂ v z) (map-comp x y) ∙ map-comp (mu x y) z ∙ ! (ap (λ v → v) (al x y z))) ] ×               
              [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
                [ ( linv₂ , map-linv ) ∈
                  Σ ((x : G₁) → mu₂ (inv₂ x) x == id₂)
                    (λ linv₂ →
                      (x : G₁) →
                        ! (ap (λ z → mu₂ z x) (map-inv x))
                          ==
                        map-comp (inv x) x ∙ ap (λ v → v) (linv x) ∙ ! map-id ∙ ! (linv₂ x)) ] ×
                  [ ( rinv₂ , map-rinv ) ∈
                    Σ ((x : G₁) → id₂ == mu₂ x (inv₂ x))
                      (λ rinv₂ →
                        (x : G₁) →
                          ! (ap (mu₂ x) (map-inv x))
                            ==
                          map-comp x (inv x) ∙ ! (ap (λ v → v) (rinv x)) ∙ ! map-id ∙ rinv₂ x) ] ×
                    [ tr₂ ∈ ((x y : G₁) → ap (λ z → mu₂ z y) (rho₂ x) == ! (al₂ x id₂ y) ∙ ap (mu₂ x) (lam₂ y)) ] ×
                      [ pent₂ ∈ ((w x y z : G₁) →
                          al₂ w x (mu₂ y z) ∙ al₂ (mu₂ w x) y z
                            ==
                          ap (mu₂ w) (al₂ x y z) ∙ al₂ w (mu₂ x y) z ∙ ap (λ v → mu₂ v z) (al₂ w x y)) ] ×
                        [ zz₁₂ ∈
                            ((x : G₁) →
                              lam₂ x
                                ==
                              ap (λ z → mu₂ z x) (rinv₂ x) ∙ ! (al₂ x (inv₂ x) x) ∙ ap (mu₂ x) (linv₂ x) ∙ rho₂ x) ] ×
                          ((x : G₁) →
                            ! (lam₂ (inv₂ x))
                              ==
                            ! (rho₂ (inv₂ x)) ∙
                            ap (mu₂ (inv₂ x)) (rinv₂ x) ∙
                            al₂ (inv₂ x) x (inv₂ x) ∙
                            ap (λ z → mu₂ z (inv₂ x)) (linv₂ x))
      ≃⟨ Σ-contr-red {A = Σ (G₁ → G₁ → G₁) (λ mu₂ → (x y : G₁) → mu₂ x y == mu x y)} (funhom-iter-contr-to (S I) mu) ⟩
    [ ( id₂ , map-id ) ∈ Σ G₁ (λ id₂ → id₂ == id) ] ×
      [ ( lam₂ , map-lam ) ∈
        Σ ((x : G₁) → mu id₂ x == x)
          (λ lam₂ →
            (x : G₁) → ! (lam₂ x) == ! (ap (λ v → v) (lam x)) ∙ ! (ap (λ z → mu z x) map-id)) ] ×
        [ ( rho₂ , map-rho ) ∈
          Σ ((x : G₁) → mu x id₂ == x)
            (λ rho₂ →
              (x : G₁) → idp == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ ap (mu x) map-id) ] ×
          [ ( al₂ , map-al ) ∈
            Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
              (λ al₂ →
                (x y z : G₁) →
                  ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z))) ] ×               
            [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
              [ ( linv₂ , map-linv ) ∈
                Σ ((x : G₁) → mu (inv₂ x) x == id₂)
                  (λ linv₂ →
                    (x : G₁) →
                      ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! map-id ∙ ! (linv₂ x)) ] ×
                [ ( rinv₂ , map-rinv ) ∈
                  Σ ((x : G₁) → id₂ == mu x (inv₂ x))
                    (λ rinv₂ →
                      (x : G₁) →
                        ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ ! map-id ∙ rinv₂ x) ] ×
                  [ tr₂ ∈ ((x y : G₁) → ap (λ z → mu z y) (rho₂ x) == ! (al₂ x id₂ y) ∙ ap (mu x) (lam₂ y)) ] ×
                    [ pent₂ ∈ ((w x y z : G₁) →
                        al₂ w x (mu y z) ∙ al₂ (mu w x) y z
                          ==
                        ap (mu w) (al₂ x y z) ∙ al₂ w (mu x y) z ∙ ap (λ v → mu v z) (al₂ w x y)) ] ×
                      [ zz₁₂ ∈
                          ((x : G₁) →
                            lam₂ x
                              ==
                            ap (λ z → mu z x) (rinv₂ x) ∙ ! (al₂ x (inv₂ x) x) ∙ ap (mu x) (linv₂ x) ∙ rho₂ x) ] ×
                        ((x : G₁) →
                          ! (lam₂ (inv₂ x))
                            ==
                          ! (rho₂ (inv₂ x)) ∙
                          ap (mu (inv₂ x)) (rinv₂ x) ∙
                          al₂ (inv₂ x) x (inv₂ x) ∙
                          ap (λ z → mu z (inv₂ x)) (linv₂ x))
      ≃⟨ Σ-contr-red {A = Σ G₁ (λ id₂ → id₂ == id)} (pathto-is-contr id) ⟩
    [ ( lam₂ , map-lam ) ∈
      Σ ((x : G₁) → mu id x == x)
        (λ lam₂ →
          (x : G₁) → ! (lam₂ x) == ! (ap (λ v → v) (lam x)) ∙ idp) ] ×
      [ ( rho₂ , map-rho ) ∈
        Σ ((x : G₁) → mu x id == x)
          (λ rho₂ →
            (x : G₁) → idp == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ idp) ] ×
        [ ( al₂ , map-al ) ∈
          Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
            (λ al₂ →
              (x y z : G₁) →
                ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z))) ] ×               
          [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
            [ ( linv₂ , map-linv ) ∈
              Σ ((x : G₁) → mu (inv₂ x) x == id)
                (λ linv₂ →
                  (x : G₁) →
                    ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
              [ ( rinv₂ , map-rinv ) ∈
                Σ ((x : G₁) → id == mu x (inv₂ x))
                  (λ rinv₂ →
                    (x : G₁) →
                      ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
                [ tr₂ ∈ ((x y : G₁) → ap (λ z → mu z y) (rho₂ x) == ! (al₂ x id y) ∙ ap (mu x) (lam₂ y)) ] ×
                  [ pent₂ ∈ ((w x y z : G₁) →
                      al₂ w x (mu y z) ∙ al₂ (mu w x) y z
                        ==
                      ap (mu w) (al₂ x y z) ∙ al₂ w (mu x y) z ∙ ap (λ v → mu v z) (al₂ w x y)) ] ×
                    [ zz₁₂ ∈
                        ((x : G₁) →
                          lam₂ x
                            ==
                          ap (λ z → mu z x) (rinv₂ x) ∙ ! (al₂ x (inv₂ x) x) ∙ ap (mu x) (linv₂ x) ∙ rho₂ x) ] ×
                      ((x : G₁) →
                        ! (lam₂ (inv₂ x))
                          ==
                        ! (rho₂ (inv₂ x)) ∙
                        ap (mu (inv₂ x)) (rinv₂ x) ∙
                        al₂ (inv₂ x) x (inv₂ x) ∙
                        ap (λ z → mu z (inv₂ x)) (linv₂ x)) ≃∎

  2grphomf-Σ-contr1 =
    [ ( lam₂ , map-lam ) ∈
      Σ ((x : G₁) → mu id x == x)
        (λ lam₂ →
          (x : G₁) → ! (lam₂ x) == ! (ap (λ v → v) (lam x)) ∙ idp) ] ×
      [ ( rho₂ , map-rho ) ∈
        Σ ((x : G₁) → mu x id == x)
          (λ rho₂ →
            (x : G₁) → idp == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ idp) ] ×
        [ ( al₂ , map-al ) ∈
          Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
            (λ al₂ →
              (x y z : G₁) →
                ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z))) ] ×               
          [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
            [ ( linv₂ , map-linv ) ∈
              Σ ((x : G₁) → mu (inv₂ x) x == id)
                (λ linv₂ →
                  (x : G₁) →
                    ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
              [ ( rinv₂ , map-rinv ) ∈
                Σ ((x : G₁) → id == mu x (inv₂ x))
                  (λ rinv₂ →
                    (x : G₁) →
                      ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
                [ tr₂ ∈ ((x y : G₁) → ap (λ z → mu z y) (rho₂ x) == ! (al₂ x id y) ∙ ap (mu x) (lam₂ y)) ] ×
                  [ pent₂ ∈ ((w x y z : G₁) →
                      al₂ w x (mu y z) ∙ al₂ (mu w x) y z
                        ==
                      ap (mu w) (al₂ x y z) ∙ al₂ w (mu x y) z ∙ ap (λ v → mu v z) (al₂ w x y)) ] ×
                    [ zz₁₂ ∈
                        ((x : G₁) →
                          lam₂ x
                            ==
                          ap (λ z → mu z x) (rinv₂ x) ∙ ! (al₂ x (inv₂ x) x) ∙ ap (mu x) (linv₂ x) ∙ rho₂ x) ] ×
                      ((x : G₁) →
                        ! (lam₂ (inv₂ x))
                          ==
                        ! (rho₂ (inv₂ x)) ∙
                        ap (mu (inv₂ x)) (rinv₂ x) ∙
                        al₂ (inv₂ x) x (inv₂ x) ∙
                        ap (λ z → mu z (inv₂ x)) (linv₂ x))
      ≃⟨ Σ-contr-red
           {A = Σ ((x : G₁) → mu id x == x) (λ lam₂ → (x : G₁) → ! (lam₂ x) == ! (ap (λ v → v) (lam x)) ∙ idp)}
           (equiv-preserves-level choice) ⟩
    [ ( rho₂ , map-rho ) ∈
      Σ ((x : G₁) → mu x id == x)
        (λ rho₂ →
          (x : G₁) → idp == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ idp) ] ×
      [ ( al₂ , map-al ) ∈
        Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
          (λ al₂ →
            (x y z : G₁) →
              ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z))) ] ×               
        [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
          [ ( linv₂ , map-linv ) ∈
            Σ ((x : G₁) → mu (inv₂ x) x == id)
              (λ linv₂ →
                (x : G₁) →
                  ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
            [ ( rinv₂ , map-rinv ) ∈
              Σ ((x : G₁) → id == mu x (inv₂ x))
                (λ rinv₂ →
                  (x : G₁) →
                    ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
              [ tr₂ ∈ _ ] ×
                [ pent₂ ∈ ((w x y z : G₁) →
                    al₂ w x (mu y z) ∙ al₂ (mu w x) y z
                      ==
                    ap (mu w) (al₂ x y z) ∙ al₂ w (mu x y) z ∙ ap (λ v → mu v z) (al₂ w x y)) ] ×
                  [ zz₁₂ ∈ _ ] × _
        ≃⟨ Σ-contr-red
             {A = Σ ((x : G₁) → mu x id == x) (λ rho₂ → (x : G₁) → idp == ap (λ v → v) (rho x) ∙ ! (rho₂ x) ∙ idp)}
             (equiv-preserves-level choice
               {{Π-level λ x → equiv-preserves-level (Σ-emap-r (λ r → pre-rotate-in-≃-back (! r ∙ idp) (ap (λ v → v) (rho x))))}}) ⟩
      [ ( al₂ , map-al ) ∈
        Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
          (λ al₂ →
            (x y z : G₁) →
              ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z))) ] ×               
        [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
          [ ( linv₂ , map-linv ) ∈
            Σ ((x : G₁) → mu (inv₂ x) x == id)
              (λ linv₂ →
                (x : G₁) →
                  ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
            [ ( rinv₂ , map-rinv ) ∈
              Σ ((x : G₁) → id == mu x (inv₂ x))
                (λ rinv₂ →
                  (x : G₁) →
                    ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
              [ tr₂ ∈ _ ] ×
                [ pent₂ ∈ ((w x y z : G₁) →
                    al₂ w x (mu y z) ∙ al₂ (mu w x) y z
                      ==
                    ap (mu w) (al₂ x y z) ∙ al₂ w (mu x y) z ∙ ap (λ v → mu v z) (al₂ w x y)) ] ×
                  [ zz₁₂ ∈ _ ] × _
      ≃⟨ Σ-contr-red
           {A =
             Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
               (λ al₂ → (x y z : G₁) → ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z)))}
           (equiv-preserves-level (choice ∘e Π-emap-r (λ _ → choice) ∘e Π-emap-r (λ _ → Π-emap-r (λ _ → choice)))) ⟩
    [ ( inv₂ , map-inv ) ∈ Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x) ] ×
      [ ( linv₂ , map-linv ) ∈
        Σ ((x : G₁) → mu (inv₂ x) x == id)
          (λ linv₂ →
            (x : G₁) →
              ! (ap (λ z → mu z x) (map-inv x)) == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
        [ ( rinv₂ , map-rinv ) ∈
          Σ ((x : G₁) → id == mu x (inv₂ x))
            (λ rinv₂ →
              (x : G₁) →
                ! (ap (mu x) (map-inv x)) == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
          [ tr₂ ∈ _ ] × [ pent₂ ∈ _ ] × [ zz₁₂ ∈ _ ] × _
      ≃⟨ Σ-contr-red {A = Σ (G₁ → G₁) (λ inv₂ → (x : G₁) → inv₂ x == inv x)} funhom-contr-to ⟩
    [ ( linv₂ , map-linv ) ∈
      Σ ((x : G₁) → mu (inv x) x == id)
        (λ linv₂ → (x : G₁) → idp == ap (λ v → v) (linv x) ∙ ! (linv₂ x)) ] ×
      [ ( rinv₂ , map-rinv ) ∈
        Σ ((x : G₁) → id == mu x (inv x))
          (λ rinv₂ → (x : G₁) → idp == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
        [ tr₂ ∈ _ ] × [ pent₂ ∈ _ ] × [ zz₁₂ ∈ _ ] × _
      ≃⟨ Σ-contr-red
           {A = Σ ((x : G₁) → mu (inv x) x == id) (λ linv₂ → (x : G₁) → idp == ap (λ v → v) (linv x) ∙ ! (linv₂ x))}
           (equiv-preserves-level choice
             {{Π-level (λ x →
               (equiv-preserves-level (Σ-emap-r (λ l → pre-rotate-in-≃-back (! l) (ap (λ v → v) (linv x))))))}}) ⟩
    [ ( rinv₂ , map-rinv ) ∈
      Σ ((x : G₁) → id == mu x (inv x))
        (λ rinv₂ → (x : G₁) → idp == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x) ] ×
      [ tr₂ ∈ _ ] × [ pent₂ ∈ _ ] × [ zz₁₂ ∈ _ ] × _
      ≃⟨ Σ-contr-red
           {A = Σ ((x : G₁) → id == mu x (inv x)) (λ rinv₂ → (x : G₁) → idp == ! (ap (λ v → v) (rinv x)) ∙ rinv₂ x)}
           (equiv-preserves-level choice
             {{Π-level (λ x →
               (equiv-preserves-level (Σ-emap-r (λ r → pre-rotate-in-!≃-back r (ap (λ v → v) (rinv x))))))}}) ⟩
    [ tr₂ ∈ _ ] × [ pent₂ ∈ _ ] × [ zz₁₂ ∈ _ ] × _
      ≃⟨ contr-is-Unit (inhab-prop-is-contr (tr-inhab , pent-inhab , zz₁-inhab , zz₂-inhab)
           {{Σ-level-instance {{Π-level-instance}}
           {{Σ-level-instance {{Π-level-instance}}
           {{Σ-level-instance {{Π-level-instance}} {{Π-level-instance}}}}}}}}) ⟩
    Unit ≃∎

  abstract
    2grphomf-Σ-contr : Θ ≃ Unit
    2grphomf-Σ-contr = 2grphomf-Σ-contr1 ∘e 2grphomf-Σ-contr0
