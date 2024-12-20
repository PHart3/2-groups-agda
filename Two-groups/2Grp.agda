{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module 2Grp where

{-
  coherent 2-group structure on a type
  following Baez and Lauda (2004)
-}

record CohGrp {i} {X : Type i} : Type i where
  constructor cohgrp
  field
    {{1trunc}} : has-level 1 X
    
    {-
      monoidal groupoid structure on X (with
      X viewed as a category with == as hom)
    -}
    id : X
    mu : X → X → X
    lam : (x : X) → mu id x == x
    rho : (x : X) → mu x id == x
    al : (x y z : X) → mu x (mu y z) == mu (mu x y) z
    tr : (x y : X) → ap (mu x) (lam y) == al x id y ∙ ap (λ z → mu z y ) (rho x)
    pent : (w x y z : X) →
      al w x (mu y z) ∙ al (mu w x) y z
      ==
      ap (mu w) (al x y z) ∙ al w (mu x y) z ∙ ap (λ v → mu v z) (al w x y)
    inv : X → X
    rinv : (x : X) → id == mu x (inv x)
    linv : (x : X) → mu (inv x) x == id
    
    -- adjoint equiv conditions on inv ("zz" short for "zig-zag")
    zz₁ : (x : X) →
      lam x ∙ ! (rho x)
      ==
      ap (λ z → mu z x) (rinv x) ∙ ! (al x (inv x) x) ∙ ap (mu x) (linv x)
    zz₂ : (x : X) →
      rho (inv x) ∙ ! (lam (inv x))
      ==
      ap (mu (inv x)) (rinv x) ∙ al (inv x) x (inv x) ∙ ap (λ z → mu z (inv x)) (linv x)
