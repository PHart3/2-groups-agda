{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import 2GrpPropsMap
open import 2GrpPropsMap2
open import 2GrpHom2
open import 2GrpHom5
open import 2GrpHom9

module 2GrpHomEq where

open CohGrp {{...}}

-- equivalence between full and short definition of 2-group morphism

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) where

  open WkSGrpHomStr {{...}}
  open CohGrpHomStrFull {{...}} hiding (map-comp; map-al)

  ForgMap : CohGrpHomStrFull map → CohGrpHomStr map
  WkSGrpHomStr.map-comp (ForgMap ρ) = CohGrpHomStrFull.map-comp ρ
  WkSGrpHomStr.map-al (ForgMap ρ) = CohGrpHomStrFull.map-al ρ

  FreeMap : {{ρ : CohGrpHomStr map}} → CohGrpHomStrFull map
  CohGrpHomStrFull.map-comp (FreeMap ⦃ ρ ⦄) = map-comp
  CohGrpHomStrFull.map-al (FreeMap ⦃ ρ ⦄) = map-al
  CohGrpHomStrFull.map-id (FreeMap ⦃ ρ ⦄) = 
    ! (al (inv (map id)) (map id) id ∙
      ap2 mu (linv (map id)) idp ∙
      lam id) ∙
    ap (mu (inv (map id)))
      (rho (map id) ∙
      ! (ap map (rho id)) ∙
      ! (map-comp id id)) ∙
    al (inv (map id)) (map id) (map id) ∙
    ap2 mu (linv (map id)) idp ∙
    lam (map id) 
  CohGrpHomStrFull.map-rho (FreeMap ⦃ ρ ⦄) x =
    =ₛ-out (map-id-map-rho map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}}) x (!ₛ
      (rhoid-to-rho map map-comp (λ x y z → =ₛ-in (map-al x y z)) (map-id {{r = FreeMap ⦃ ρ ⦄}})
        (map-id-map-rho map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}}) id (=ₛ-in idp)) x)))
  CohGrpHomStrFull.map-lam (FreeMap ⦃ ρ ⦄) x =
    ! (=ₛ-out (map-id-map-lam map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}}) x (
      !ₛ (rho-to-lam map map-comp (λ x y z → =ₛ-in (map-al x y z)) (map-id {{r = FreeMap ⦃ ρ ⦄}})
        (=ₛ-in (map-rho {{r = FreeMap ⦃ ρ ⦄}} id)) x))))
  CohGrpHomStrFull.map-inv (FreeMap ⦃ ρ ⦄) x = 
    ! (al (inv (map x)) (map x) (inv (map x)) ∙
      ap2 mu (linv (map x)) idp ∙
      lam (inv (map x))) ∙
    ap (mu (inv (map x)))
      (! (rinv (map x)) ∙
      map-id {{r = FreeMap ⦃ ρ ⦄}} ∙
      ap map (rinv x) ∙
      ! (map-comp x (inv x))) ∙
    al (inv (map x)) (map x) (map (inv x)) ∙
    ap2 mu (linv (map x)) idp ∙
    lam (map (inv x))
  CohGrpHomStrFull.map-rinv (FreeMap ⦃ ρ ⦄) x = 
    =ₛ-out (!ₛ (map-inv-map-rinv map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}}) (map-inv {{r = FreeMap ⦃ ρ ⦄}}) x (=ₛ-in idp)))
  CohGrpHomStrFull.map-linv (FreeMap ⦃ ρ ⦄) x =
    ! ( =ₛ-out (
      map-inv-map-linv map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}}) (map-inv {{r = FreeMap ⦃ ρ ⦄}}) x
        (!ₛ (
          rinv-to-linv map map-comp (map-id {{r = FreeMap ⦃ ρ ⦄}})
            map-al-rot2
            (map-inv {{r = FreeMap ⦃ ρ ⦄}})
            (λ x → =ₛ-in (map-rho {{r = FreeMap ⦃ ρ ⦄}} x))
            (λ x → =ₛ-in (map-lam {{r = FreeMap ⦃ ρ ⦄}} x))
            x (=ₛ-in (map-rinv {{r = FreeMap ⦃ ρ ⦄}} x))))))

  abstract
    Forg-equiv : is-equiv ForgMap
    Forg-equiv =
      is-eq ForgMap (λ ρ → FreeMap {{ρ}})
        (λ _ → idp)
        λ α → ! (2grphomfulleq map {{α}} _ _ _ _ _ _
          (! (=ₛ-out (Λ α)))
          (λ= λ x → ! (=ₛ-out (map-rinv-map-inv map (map-comp {{r = ForgMap α}})
            (map-id {{r = FreeMap {{ForgMap α}}}}) (map-inv {{r = α}})
            (λ z → =ₛ-in (map-rinv {{r = α}} z) ∙ₛ lemma α z) x))))
      where
        Λ : (α : CohGrpHomStrFull map) → 
          map-id {{r = α}} ◃∎
            =ₛ
          ! (al (inv (map id)) (map id) id ∙
            ap2 mu (linv (map id)) idp ∙
            lam id) ◃∙
          ap (mu (inv (map id))) (
            rho (map id) ∙
            ! (ap map (rho id)) ∙
            ! (map-comp {{r = ForgMap α}} id id)) ◃∙
          al (inv (map id)) (map id) (map id) ◃∙
          ap2 mu (linv (map id)) idp ◃∙
          lam (map id) ◃∎
        Λ α =
          map-rho-map-id map (map-comp {{r = ForgMap α}}) (map-id {{r = α}}) id
            (=ₛ-in (map-rho {{r = α}} id))

        lemma : (α : CohGrpHomStrFull map) (z : G₁) →
          map-comp {{r = ForgMap α}} z (inv z) ◃∙
          ! (ap map (rinv z)) ◃∙
          ! (map-id {{r = α}}) ◃∙
          rinv (map z) ◃∎
            =ₛ
          map-comp {{r = ForgMap α}} z (inv z) ◃∙
          ! (ap map (rinv z)) ◃∙
          ! (map-id {{r = FreeMap {{ForgMap α}}}}) ◃∙
          rinv (map z) ◃∎
        lemma α z =
          map-comp {{r = ForgMap α}} z (inv z) ◃∙
          ! (ap map (rinv z)) ◃∙
          ! (map-id {{r = α}}) ◃∙
          rinv (map z) ◃∎
            =ₛ₁⟨ 2 & 1 &
              ap ! (=ₛ-out (Λ α)) ⟩
          map-comp {{r = ForgMap α}} z (inv z) ◃∙
          ! (ap map (rinv z)) ◃∙
          ! (map-id {{r = FreeMap {{ForgMap α}}}}) ◃∙
          rinv (map z) ◃∎ ∎ₛ

  2GrpHomf-≃ : CohGrpHomStrFull map ≃ CohGrpHomStr map
  2GrpHomf-≃ = ForgMap , Forg-equiv
