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

  open CohGrpHomStr
  open CohGrpHomStrFull

  -- forgetful map
  ForgMap : CohGrpHomStrFull map → CohGrpHomStr map
  map-comp (ForgMap ρ) = map-comp ρ
  map-al (ForgMap ρ) = map-al ρ

  Forg-equiv : is-equiv ForgMap
  Forg-equiv = {!!}
