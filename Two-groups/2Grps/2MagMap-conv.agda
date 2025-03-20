{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpMap
open import NatIso

module 2MagMap-conv where

open CohGrp {{...}}
open WkMagNatIso

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}} where

  tri-conv :
    (iso₂ : WkMagNatIso (grphom-forg f₁) (grphom-forg f₁'))
    (iso₃ : WkMagNatIso (grphom-forg f₂) (grphom-forg f₂'))
    (iso₁ : WkMagNatIso (grphom-forg (f₂ ∘2G f₁')) (grphom-forg (f₂' ∘2G f₁))) →
    =WkMagNatIso iso₁ ((natiso-whisk-r iso₃) natiso-∘ (!ʷ (natiso-whisk-l iso₂)))
    →
    natiso2G-to-== iso₁
      ==
    ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
    ap (λ m → m ∘2G f₁) (natiso2G-to-== iso₃)
  tri-conv iso₂ = natiso2G-ind
    (λ f iso → 
      (iso₁ : WkMagNatIso (grphom-forg (f₂ ∘2G f₁')) (grphom-forg (f ∘2G f₁))) →
      =WkMagNatIso iso₁ ((natiso-whisk-r iso) natiso-∘ (!ʷ (natiso-whisk-l iso₂)))
      →
      natiso2G-to-== iso₁
        ==
      ! (ap (λ m → f₂ ∘2G m) (natiso2G-to-== iso₂)) ∙
      ap (λ m → m ∘2G f₁) (natiso2G-to-== iso))
    {!!}
