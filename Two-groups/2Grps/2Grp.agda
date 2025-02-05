{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Magma

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
    tr : (x y : X) → ap (λ z → mu z y) (rho x) == ! (al x id y) ∙ ap (mu x) (lam y)
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
      lam x
      ==
      ap (λ z → mu z x) (rinv x) ∙
      ! (al x (inv x) x) ∙
      ap (mu x) (linv x) ∙
      rho x
    zz₂ : (x : X) →
      ! (lam (inv x))
      ==
      ! (rho (inv x)) ∙
      ap (mu (inv x)) (rinv x) ∙
      al (inv x) x (inv x) ∙
      ap (λ z → mu z (inv x)) (linv x)

-- underlying 2-magma structure of a 2-group
module _ {i} {G : Type i} where

  mag : CohGrp G → WkMag G
  mag η = cohgrp (mu η) (al η) where open CohGrp

  instance
    mag-instance : {{η : CohGrp G}} → WkMag G
    mag-instance {{η}} = mag η

open CohGrp {{...}}

-- multiplication by id is an iso in all monoidal cats
module _ {i} {G : Type i} {{η : CohGrp G}} where

  muid-iso : is-equiv (mu id)
  muid-iso =
    ∼-preserves-equiv
    (λ x → ! (lam x))
    (idf-is-equiv G)

  -- <– (ap-equiv (muid , muid-iso) _ _)
  muid-iso<– : (z₁ z₂ : G) → (mu id z₁ == mu id z₂) → (z₁ == z₂)
  muid-iso<– z₁ z₂ p = 
    ! (ap (λ x → x) (! (! (lam z₁))) ∙ idp) ∙
    ap (λ x → x) p ∙
    ap (λ x → x) (! (! (lam z₂))) ∙
    idp

  idmu-iso : is-equiv (λ x → mu x id)
  idmu-iso =
    ∼-preserves-equiv
    (λ x → ! (rho x))
    (idf-is-equiv G)

  -- <– (ap-equiv ((λ x → mu x id) , idmu-iso) _ _)
  idmu-iso<– : (z₁ z₂ : G) → (mu z₁ id == mu z₂ id) → (z₁ == z₂)
  idmu-iso<– z₁ z₂ p = 
    ! (ap (λ x → x) (! (! (rho z₁))) ∙ idp) ∙
    ap (λ x → x) p ∙
    ap (λ x → x) (! (! (rho z₂))) ∙
    idp

-- multiplication on either side is an iso
module _ {i} {G : Type i} {{η : CohGrp G}} (x : G) where

  mu-pre-iso : is-equiv (mu x)
  mu-pre-iso =
    is-eq (mu x) (mu (inv x))
      (λ b → al x (inv x) b ∙ ap2 mu (! (rinv x)) idp ∙ lam b)
      λ a → al (inv x) x a ∙ ap2 mu (linv x) idp ∙ lam a

  mu-pre-ff<– : (z₁ z₂ : G) → (mu x z₁ == mu x z₂) → (z₁ == z₂)
  mu-pre-ff<– z₁ z₂ p =
    ! (al (inv x) x z₁ ∙ ap2 mu (linv x) idp ∙ lam z₁) ∙
    ap (mu (inv x)) p ∙
    al (inv x) x z₂ ∙
    ap2 mu (linv x) idp ∙
    lam z₂

  mu-post-iso : is-equiv (λ z → mu z x)
  mu-post-iso =
    is-eq (λ z → mu z x) (λ z → mu z (inv x))
      (λ b → ! (al b (inv x) x) ∙ ap (mu b) (linv x) ∙ rho b )
      λ a → ! (al a x (inv x)) ∙ ! (ap (mu a) (rinv x)) ∙ rho a

  mu-post-ff<– : (z₁ z₂ : G) → (mu z₁ x == mu z₂ x) → (z₁ == z₂)
  mu-post-ff<– z₁ z₂ p =
    ! (! (al z₁ x (inv x)) ∙ ! (ap (mu z₁) (rinv x)) ∙ rho z₁) ∙
    ap (λ z → mu z (inv x)) p ∙
    ! (al z₂ x (inv x)) ∙
    ! (ap (mu z₂) (rinv x)) ∙
    rho z₂

-- morphisms of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  -- definition explicitly accounting for all 2-group data
  record CohGrpHomStrFull (map : G₁ → G₂) : Type (lmax i j) where
    constructor cohgrphomstrfull
    field
      map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)
      map-al : (x y z : G₁) →
        ! (al (map x) (map y) (map z)) ∙
        ap (mu (map x)) (map-comp y z) ∙
        map-comp x (mu y z)
        ==
        ap (λ v → mu v (map z)) (map-comp x y) ∙
        map-comp (mu x y) z ∙
        ! (ap map (al x y z))
      map-id : id == map id
      map-rho : (x : G₁) →
        ! (map-comp x id)
        ==
        ap map (rho x) ∙
        ! (rho (map x)) ∙
        ap (mu (map x)) map-id
      map-lam : (x : G₁) →
        ! (lam (map x))
        ==
        ! (ap map (lam x)) ∙
        ! (map-comp id x) ∙
        ! (ap (λ z → mu z (map x)) map-id)
      map-inv : (x : G₁) → inv (map x) == map (inv x)
      map-rinv : (x : G₁) →
        ! (ap (mu (map x)) (map-inv x))
        ==
        map-comp x (inv x) ∙
        ! (ap map (rinv x)) ∙
        ! map-id ∙
        rinv (map x)
      map-linv : (x : G₁) → 
        ! (ap (λ z → mu z (map x)) (map-inv x))
        ==
        map-comp (inv x) x ∙
        ap map (linv x) ∙
        ! map-id ∙
        ! (linv (map x))

  -- shorter definition, easier to work with
  CohGrpHomStr : (map : G₁ → G₂) → Type (lmax i j)
  CohGrpHomStr map = WkMagHomStr {{mag η₁}} {{mag η₂}} map

  record CohGrpHom : Type (lmax i j) where
    constructor cohgrphom
    field
      map : G₁ → G₂
      {{str}} : CohGrpHomStr map
  open CohGrpHom

  grphom-forg : CohGrpHom → WkMagWkHom
  map-wk (grphom-forg f) = map f
  map-comp-wk (grphom-forg f) = map-comp (str f) where open WkMagHomStr

  -- natural isomorphisms between 2-group morphisms

  CohGrpNatIso : CohGrpHom → CohGrpHom → Type (lmax i j)
  CohGrpNatIso μ₁ μ₂ = WkMagNatIso (grphom-forg μ₁) (grphom-forg μ₂)

-- categorical structure on 2-groups

open CohGrpHom

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open WkMagHomStr

  idf2G : CohGrpHomStr (idf G)
  map-comp idf2G x y = idp
  map-al idf2G x y z = ∙-unit-r (! (al x y z)) ∙ ap ! (! (ap-idf (al x y z)))

module _{i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  open WkMagHomStr {{...}}

  -- composition of 2-group morphisms
  infixr 60 _∘2Gσ_
  _∘2Gσ_ :  (F₂ : CohGrpHom {{η₂}} {{η₃}}) (F₁ : CohGrpHom {{η₁}} {{η₂}}) → CohGrpHomStr (map F₂ ∘ map F₁)
  _∘2Gσ_ F₂ F₁ = cohmaghom (map F₂) ∘2Mσ cohmaghom (map F₁)

  infixr 50 _∘2G_
  _∘2G_ : CohGrpHom {{η₂}} {{η₃}} → CohGrpHom {{η₁}} {{η₂}} → CohGrpHom {{η₁}} {{η₃}}
  map (F₂ ∘2G F₁) = map F₂ ∘ map F₁
  str (F₂ ∘2G F₁) = F₂ ∘2Gσ F₁
