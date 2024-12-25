{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp

module Hmtpy2Grp where

-- homotopy 2-groups of 2-types (i.e., loop spaces)

module _ {i} {X : Type i} {{tr : has-level 2 X}} where

  Loop2Grp : (x : X) → CohGrp (x == x)
  CohGrp.1trunc (Loop2Grp x) =  has-level-apply tr x x
  CohGrp.id (Loop2Grp x) = idp
  CohGrp.mu (Loop2Grp x) = _∙_
  CohGrp.lam (Loop2Grp x) x₁ = idp
  CohGrp.rho (Loop2Grp x) x₁ = ∙-unit-r x₁
  CohGrp.al (Loop2Grp x) x₁ y z = ! (∙-assoc x₁ y z)
  CohGrp.tr (Loop2Grp x) x₁ y = {!!}
  CohGrp.pent (Loop2Grp x) w x₁ y z = {!!}
  CohGrp.inv (Loop2Grp x) x₁ = {!!}
  CohGrp.rinv (Loop2Grp x) x₁ = {!!}
  CohGrp.linv (Loop2Grp x) x₁ = {!!}
  CohGrp.zz₁ (Loop2Grp x) x₁ = {!!}
  CohGrp.zz₂ (Loop2Grp x) x₁ = {!!}

-- Loop induces a morphism of 2-groups.

module _ {i j} {G₁ : Type i} (η : CohGrp G₁)
  (G₂ : Type j) (b : G₂) {{_ : has-level 2 G₂}} where
  
--  Hom (G₁ , η) (G₂ == G₂ , Loop2Grp G₂)

