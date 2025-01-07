{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpPropsMap
open import 2GrpHom2
open import 2GrpHom5

module 2GrpHomEq where

open CohGrp {{...}}

-- equivalence between full and short definition of 2-group morphism

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) where

  open CohGrpHomStr {{...}}

  ForgMap : CohGrpHomStrFull map → CohGrpHomStr map
  CohGrpHomStr.map-comp (ForgMap ρ) = CohGrpHomStrFull.map-comp ρ
  CohGrpHomStr.map-al (ForgMap ρ) = CohGrpHomStrFull.map-al ρ

  FreeMap : {{ρ : CohGrpHomStr map}} → CohGrpHomStrFull map
  CohGrpHomStrFull.map-comp (FreeMap ⦃ ρ ⦄) = map-comp
  CohGrpHomStrFull.map-al (FreeMap ⦃ ρ ⦄) = map-al
  CohGrpHomStrFull.map-id (FreeMap ⦃ ρ ⦄) = {!!}
  CohGrpHomStrFull.map-inv (FreeMap ⦃ ρ ⦄) = {!!}
  CohGrpHomStrFull.map-rinv (FreeMap ⦃ ρ ⦄) = {!!}
  CohGrpHomStrFull.map-lam (FreeMap ⦃ ρ ⦄) = {!!}
  CohGrpHomStrFull.map-rho (FreeMap ⦃ ρ ⦄) = {!!}
  CohGrpHomStrFull.map-linv (FreeMap ⦃ ρ ⦄) = {!!}

{-
  Forg-equiv : is-equiv ForgMap
  Forg-equiv =
    is-eq ForgMap (λ ρ → FreeMap {{ ρ }})
    (λ b → idp)
    {!!}
-}
