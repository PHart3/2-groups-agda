{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import 2Grp
open import 2MagMap
open import 2GrpMap
open import NatIso
open import 2GrpSIP

-- the bicategory of 2-groups

module 2Grp-bc where

open import 2Grp

module _ {i : ULevel} where

  open BicatStr

  2grp-bicat : BicatStr i (Σ (Type i) (λ G → CohGrp G))
  hom 2grp-bicat (G₁ , η₁) (G₂ , η₂) = CohGrpHom {{η₁}} {{η₂}}
  id₁ 2grp-bicat (G , η) = cohgrphom (idf G) {{idf2G {{η}}}}
  _◻_ 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} f₂ f₁ = _∘2G_ {{η₁}} {{η₂}} {{η₃}} f₂ f₁
  ρ 2grp-bicat {(_ , η₁)} {(_ , η₂)} f = natiso2G-to-== {{η₁}} {{η₂}} $
    unit-wkmaghom-r {{mag (η₁)}} {{mag (η₂)}} (grphom-forg {{η₁}} {{η₂}} f)
  lamb 2grp-bicat {(_ , η₁)} {(_ , η₂)} f = natiso2G-to-== {{η₁}} {{η₂}} $
    unit-wkmaghom-l {{mag (η₁)}} {{mag (η₂)}} (grphom-forg {{η₁}} {{η₂}} f)
  α 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} {(_ , η₄)} f₃ f₂ f₁ = natiso2G-to-== {{η₁}} {{η₄}} $ 
    assoc-wkmaghom {{mag η₁}} {{mag η₂}} {{mag η₃}} {{mag η₄}}
      (grphom-forg {{η₃}} {{η₄}} f₃)
      (grphom-forg {{η₂}} {{η₃}} f₂)
      (grphom-forg {{η₁}} {{η₂}} f₁)
  tri-bc 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} f₁ f₂ = {!natiso∼-to-== {{_}} {{_}} ?!}
  pent-bc 2grp-bicat = {!!}
  hom-trunc 2grp-bicat = {!!}

  -- loop is adj equiv
