{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module 2Grp where

{-
  coherent 2-group structure on a type
  following Baez and Lauda (2004)
-}

record CohGrp {i} (X : Type i) : Type i where
  constructor cohgrp
  field
    instance {{1trunc}} : has-level 1 X
    
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
    
    -- beginning of 2-group structure
    inv : X → X
    linv : (x : X) → mu (inv x) x == id
    rinv : (x : X) → id == mu x (inv x)
    
    -- adjoint equiv conditions on inv ("zz" short for "zig-zag")
    zz₁ : (x : X) →
      lam x ∙ ! (rho x)
      ==
      ap (λ z → mu z x) (rinv x) ∙ ! (al x (inv x) x) ∙ ap (mu x) (linv x)
    zz₂ : (x : X) →
      rho (inv x) ∙ ! (lam (inv x))
      ==
      ap (mu (inv x)) (rinv x) ∙ al (inv x) x (inv x) ∙ ap (λ z → mu z (inv x)) (linv x)

open CohGrp {{...}}

-- morphisms of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  -- definition explicitly accounting for all 2-group data
  record CohGrpHomFull : Type (lmax i j) where
    constructor cohgrphomfull
    field
      map : G₁ → G₂
      map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)
      map-id : id == map id
      map-lam : (x : G₁) →
        ap (λ z → mu z (map x)) map-id ∙ map-comp id x ∙ ap map (lam x) == lam (map x)
      map-rho : (x : G₁) →
        ap (mu (map x)) map-id ∙ map-comp x id ∙ ap map (rho x) == rho (map x)
      map-al : (x y z : G₁) →
        ! (al (map x) (map y) (map z)) ∙
        ap (mu (map x)) (map-comp y z) ∙
        map-comp x (mu y z)
        ==
        ap (λ v → mu v (map z)) (map-comp x y) ∙
        map-comp (mu x y) z ∙
        ! (ap map (al x y z))
      map-inv : (x : G₁) → inv (map x) == map (inv x)
      map-linv : (x : G₁) → 
        ap (λ z → mu z (map x)) (map-inv x) ∙
        map-comp (inv x) x ∙
        ap map (linv x)
        ==
        linv (map x) ∙
        map-id
      map-rinv : (x : G₁) →
        rinv (map x) ∙
        ap (mu (map x)) (map-inv x) ∙
        map-comp x (inv x)
        ==
        map-id ∙
        ap map (rinv x)

  -- shorter definition, easier to work with
  record CohGrpHom : Type (lmax i j) where
    constructor cohgrphom
    field
      map : G₁ → G₂
      map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)
      map-al : (x y z : G₁) →
        ! (al (map x) (map y) (map z)) ∙
        ap (mu (map x)) (map-comp y z) ∙
        map-comp x (mu y z)
        ==
        ap (λ v → mu v (map z)) (map-comp x y) ∙
        map-comp (mu x y) z ∙
        ! (ap map (al x y z))
