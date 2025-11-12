{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Unit
open import lib.FTID
open import lib.NType2
open import 2Semigroup
open import 2Grp
open import 2GrpHomEq
open import 2GrpSIP-aux

module 2GrpSIP where

-- SIP for 2-groups (using the short definition of 2-group morphism)

module _ {i j} {G₁ : Type i} {G₂ : Type j} where

  infix 30 _2g≃-f_
  _2g≃-f_ : CohGrp G₁ → CohGrp G₂ → Type (lmax i j)
  η₁ 2g≃-f η₂ = Σ (G₁ ≃ G₂) (λ (map , _) → CohGrpHomStrFull {{η₁}} {{η₂}} map)

  infix 30 _2g≃_
  _2g≃_ : CohGrp G₁ → CohGrp G₂ → Type (lmax i j)
  η₁ 2g≃ η₂ = Σ (G₁ ≃ G₂) (λ (map , _) → CohGrpHomStr {{η₁}} {{η₂}} map)

  2g≃-f-≃ : (η₁ : CohGrp G₁) (η₂ : CohGrp G₂) → (η₁ 2g≃-f η₂) ≃ (η₁ 2g≃ η₂)
  2g≃-f-≃ η₁ η₂ = Σ-emap-r λ e → 2GrpHomf-≃ {{η₁}} {{η₂}} (fst e)  

ide2G : ∀ {i} {G : Type i} (η : CohGrp G) → η 2g≃ η
fst (ide2G {G = G} η) = ide G
snd (ide2G η) = idf2G {{η}}

module _ {i} (G₁ : Type i) (η₁ : CohGrp G₁) where

  open CohGrp η₁

  abstract
    2grphomf-Σ-≃ :
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
        ≃
      Σ (Σ (Type i) (λ G₂ → CohGrp G₂)) (λ (_ , η₂) → η₁ 2g≃-f η₂)
    2grphomf-Σ-≃ =
      equiv
        (λ
          (( ( G₂ , 1trunc₂ ) , φ ) , ( mu₂ , map-comp ) , (id₂ , map-id) , ( lam₂ , map-lam ) , ( rho₂ , map-rho ) ,
            ( al₂ , map-al ) , ( inv₂ , map-inv ) , ( linv₂ , map-linv ) , ( rinv₂ , map-rinv ) , tr₂ , pent₂ , zz₁₂ , zz₂₂ )
          → (G₂ , cohgrp {{1trunc₂}} id₂ mu₂ lam₂ rho₂ al₂ tr₂ pent₂ inv₂ linv₂ rinv₂ zz₁₂ zz₂₂) ,
            φ , (cohgrphomstrfull map-comp map-al map-id map-rho map-lam map-inv map-rinv map-linv))
        (λ
          (( G₂ , cohgrp {{1trunc₂}} id₂ mu₂ lam₂ rho₂ al₂ tr₂ pent₂ inv₂ linv₂ rinv₂ zz₁₂ zz₂₂ ) ,
            ( φ , cohgrphomstrfull map-comp map-al map-id map-rho map-lam map-inv map-rinv map-linv ) )
          → ((G₂ , 1trunc₂) , φ) , ((mu₂ , map-comp) , ((id₂ , map-id) , (lam₂ , map-lam) , ((rho₂ , map-rho) ,
            ((al₂ , map-al) , ((inv₂ , map-inv) , (linv₂ , map-linv) , ((rinv₂ , map-rinv) , tr₂ , pent₂ , zz₁₂ , zz₂₂)))))))
        (λ
          (( G₂ , cohgrp {{1trunc₂}} id₂ mu₂ lam₂ rho₂ al₂ tr₂ pent₂ inv₂ linv₂ rinv₂ zz₁₂ zz₂₂ ) ,
            ( φ , cohgrphomstrfull map-comp map-al map-id map-rho map-lam map-inv map-rinv map-linv ) )
          → idp)
        λ
          (( ( G₂ , 1trunc₂ ) , φ ) , ( mu₂ , map-comp ) , (id₂ , map-id) , ( lam₂ , map-lam ) , ( rho₂ , map-rho ) ,
            ( al₂ , map-al ) , ( inv₂ , map-inv ) , ( linv₂ , map-linv ) , ( rinv₂ , map-rinv ) , tr₂ , pent₂ , zz₁₂ , zz₂₂ )
          → idp

  2grphomf-contr : is-contr (Σ (Σ (Type i) (λ G₂ → CohGrp G₂)) (λ (_ , η₂) → η₁ 2g≃-f η₂))
  2grphomf-contr = equiv-preserves-level (2grphomf-Σ-≃ ∘e (2grphomf-Σ-contr G₁ η₁)⁻¹)

  2grphom-contr : is-contr (Σ (Σ (Type i) (λ G₂ → CohGrp G₂)) (λ (_ , η₂) → η₁ 2g≃ η₂))
  2grphom-contr = equiv-preserves-level (Σ-emap-r (λ (_ , η₂) → 2g≃-f-≃ η₁ η₂)) {{2grphomf-contr}}

module _ {i} {G₁ : Type i} {η₁ : CohGrp G₁} where

  2grphom-ind : ∀ {k} (P : ((_ , η₂) : Σ (Type i) (λ G₂ → CohGrp G₂)) → η₁ 2g≃ η₂ → Type k)
    → P (G₁ , η₁) (ide2G η₁) → {(G₂ , η₂) : Σ (Type i) (λ G₂ → CohGrp G₂)} (m : η₁ 2g≃ η₂) → P (G₂ , η₂) m
  2grphom-ind P = ID-ind-map P (2grphom-contr G₁ η₁)

  2grphom-to-== : {(G₂ , η₂) : Σ (Type i) (λ G₂ → CohGrp G₂)} → η₁ 2g≃ η₂ → (G₁ , η₁) == (G₂ , η₂)
  2grphom-to-== = 2grphom-ind (λ (G₂ , η₂) _ → (G₁ , η₁) == (G₂ , η₂)) idp

  2grphom-from-== : {C : Σ (Type i) (λ G₂ → CohGrp G₂)} → (G₁ , η₁) == C → η₁ 2g≃ (snd C)
  2grphom-from-== idp = ide2G η₁
