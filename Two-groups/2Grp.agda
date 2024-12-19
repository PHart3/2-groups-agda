{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module 2Grp where

-- coherent 2-group structure on a type

module _ {i} (X : Type i) where

  record CohGrp : Type i where
    constructor cohgrp
    field
      id : X
      μ : X → X → X
      lam : (x : X) → μ id x == x
      rho : (x : X) → μ x id == x
      al : (x y z : X) → μ x (μ y z) == μ (μ x y) z
      tr : (x y : X) → ap (μ x) (lam y) == al x id y ∙ ap (λ z → μ z y ) (rho x)
      pent : (w x y z : X) →
        al w x (μ y z) ∙ al (μ w x) y z
        ==
        ap (μ w) (al x y z) ∙ al w (μ x y) z ∙ ap (λ v → μ v z) (al w x y)
      inv : X → X
      linv : (x : X) → μ (inv x) x == id
      rinv : (x : X) → id == μ x (inv x)
      -- adjoint equiv conditions on inv
