{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp

module Hmtpy2Grp where

-- homotopy 2-groups of 2-types (i.e., loop spaces)

module _ {i} {X : Type i} {{trX : has-level 2 X}} where

  open CohGrp

  Loop2Grp : (x : X) → CohGrp (x == x)
  1trunc (Loop2Grp x) =  has-level-apply trX x x
  id (Loop2Grp x) = idp
  mu (Loop2Grp x) = _∙_
  lam (Loop2Grp x) p = idp
  rho (Loop2Grp x) = ∙-unit-r
  al (Loop2Grp x) p₁ p₂ p₃ = ! (∙-assoc p₁ p₂ p₃)
  tr (Loop2Grp x) = tri-id
  pent (Loop2Grp x)= pent-id
  inv (Loop2Grp x) = !
  linv (Loop2Grp x) = !-inv-l
  rinv (Loop2Grp x) p = ! (!-inv-r p)
  zz₁ (Loop2Grp x) = zz-id1
  zz₂ (Loop2Grp x) = zz-id2

-- Loop acts on morphism of 2-groups.

module _ {i j} {G₁ : Type i} (ηR : CohGrp G₁)
  (G₂ : Type j) (b : G₂) {{_ : has-level 2 G₂}} where
  
--  CohGrpHom {{ηG}} {{Loop2Grp G₂}}

