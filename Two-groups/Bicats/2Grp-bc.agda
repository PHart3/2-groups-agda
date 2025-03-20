{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import 2Grp
open import 2MagMap
open import NatIso
open import 2GrpSIP

-- the bicategory of 2-groups

module 2Grp-bc where

module _ {i : ULevel} where

  open BicatStr

  2grp-bicat : BicatStr i (Σ (Type i) (λ G → CohGrp G))
  hom 2grp-bicat (G₁ , η₁) (G₂ , η₂) = CohGrpHom {{η₁}} {{η₂}}
  id₁ 2grp-bicat (G , η) = cohgrphom (idf G) {{idf2G {{η}}}}
  _◻_ 2grp-bicat {G₁} {G₂} {G₃} f₂ f₁ = _∘2G_ {{snd G₁}} {{snd G₂}} {{snd G₃}} f₂ f₁
  ρ 2grp-bicat f = {!natiso-to-== (unit-wkmaghom-r f)!}  -- transfer results to WkMagWkHom
  lamb 2grp-bicat = {!!}
  α 2grp-bicat = {!!}
  tri-bc 2grp-bicat = {!!}
  pent-bc 2grp-bicat = {!!}
  hom-trunc 2grp-bicat = {!!}

  -- loop is adj equiv
