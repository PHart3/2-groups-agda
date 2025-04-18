{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import Bicategory
open import 2Grp
open import 2SGrpMap
open import 2GrpMap
open import 2GrpMap-conv

-- the bicategory of 2-groups

module 2Grp-bc where

2Grp-tot : (i : ULevel) → Type (lsucc i)
2Grp-tot i = Σ (Type i) (λ G → CohGrp G)

module _ (i : ULevel) where

  open BicatStr

  2grp-bicat : BicatStr i (2Grp-tot i) 
  hom 2grp-bicat (G₁ , η₁) (G₂ , η₂) = CohGrpHom {{η₁}} {{η₂}}
  id₁ 2grp-bicat (G , η) = cohgrphom (idf G) {{idf2G {{η}}}}
  _◻_ 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} f₂ f₁ = _∘2G_ {{η₁}} {{η₂}} {{η₃}} f₂ f₁
  ρ 2grp-bicat {(_ , η₁)} {(_ , η₂)} f = natiso2G-to-== {{η₁}} {{η₂}} $
    unit-wksgrphom-r {{sgrp (η₁)}} {{sgrp (η₂)}} (grphom-forg {{η₁}} {{η₂}} f)
  lamb 2grp-bicat {(_ , η₁)} {(_ , η₂)} f = natiso2G-to-== {{η₁}} {{η₂}} $
    unit-wksgrphom-l {{sgrp (η₁)}} {{sgrp (η₂)}} (grphom-forg {{η₁}} {{η₂}} f)
  α 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} {(_ , η₄)} f₃ f₂ f₁ = natiso2G-to-== {{η₁}} {{η₄}} $ 
    assoc-wksgrphom {{sgrp η₁}} {{sgrp η₂}} {{sgrp η₃}} {{sgrp η₄}}
      (grphom-forg {{η₃}} {{η₄}} f₃)
      (grphom-forg {{η₂}} {{η₃}} f₂)
      (grphom-forg {{η₁}} {{η₂}} f₁)
  tri-bc 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} f₁ f₂ = tri-2G {{η₁}} {{η₂}} {{η₃}} f₁ f₂
  pent-bc 2grp-bicat {(_ , η₁)} {(_ , η₂)} {(_ , η₃)} {(_ , η₄)} {(_ , η₅)} f₁ f₂ f₃ f₄ =
    pent-2G {{η₁}} {{η₂}} {{η₃}} {{η₄}} {{η₅}} f₁ f₂ f₃ f₄
  hom-trunc 2grp-bicat {(_ , η₁)} {(_ , η₂)} = CohGrpHom-1trunc {{η₁}} {{η₂}}

instance
  2grp-bicat-instance : ∀ {i} → BicatStr i (2Grp-tot i)
  2grp-bicat-instance {i} = 2grp-bicat i
