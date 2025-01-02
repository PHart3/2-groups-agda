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
    tr : (x y : X) → ap (mu x) (lam y) == al x id y ∙ ap (λ z → mu z y) (rho x)
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
  zz₂-rot◃ : (x : X) →
    rho (inv x) ◃∎
      =ₛ
    ap (mu (inv x)) (rinv x) ◃∙
    al (inv x) x (inv x) ◃∙
    ap (λ z → mu z (inv x)) (linv x) ◃∙
    lam (inv x) ◃∎
  zz₂-rot◃ x = !-!-seq4 _ _ _ _ _ (=ₛ-in
    (! (∙-unit-r (! (rho (inv x)))) ∙
      ap (λ p → ! (rho (inv x)) ∙ p)
        (! (!-inv-r (ap (mu (inv x)) (rinv x) ∙ al (inv x) x (inv x) ∙ ap (λ z → mu z (inv x)) (linv x)))) ∙
      ! (∙-assoc (! (rho (inv x)))
        (ap (mu (inv x)) (rinv x) ∙ al (inv x) x (inv x) ∙ ap (λ z → mu z (inv x)) (linv x)) _) ∙
      ap (λ p → p ∙ ! (ap (mu (inv x)) (rinv x) ∙
        al (inv x) x (inv x) ∙ ap (λ z → mu z (inv x)) (linv x))) (! (zz₂ x)) ∙
      ap (λ p → ! (lam (inv x)) ∙ p) (!-∙-∙ (ap (mu (inv x)) (rinv x)) (al (inv x) x (inv x)) _)))

open CohGrp {{...}}

-- multiplication on either side is an iso
module _ {i} {G : Type i} {{η : CohGrp G}} (x : G) where

  mu-pre-iso : is-equiv (mu x)
  mu-pre-iso =
    is-eq (mu x) (mu (inv x))
      (λ b → al x (inv x) b ∙ ap2 mu (! (rinv x)) idp ∙ lam b)
      λ a → al (inv x) x a ∙ ap2 mu (linv x) idp ∙ lam a

  mu-pre-ff : (z₁ z₂ : G) →  (z₁ == z₂) ≃ (mu x z₁ == mu x z₂)
  mu-pre-ff z₁ z₂ = ap-equiv (_ , mu-pre-iso) z₁ z₂

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

  zz₁-rinv-aux :
    rinv x ◃∎
      =ₛ
    ! (! (al id x (inv x)) ∙ ! (ap (mu id) (rinv x)) ∙ rho id) ◃∙
    ap (λ z → mu z (inv x))
      (lam x ∙ ! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ◃∙
    ! (al (mu x (inv x)) x (inv x)) ◃∙
    ! (ap (mu (mu x (inv x))) (rinv x)) ◃∙
    rho (mu x (inv x)) ◃∎
  zz₁-rinv-aux = =ₛ-in (
    ! (<–-inv-l (ap-equiv ((λ z → mu z x) , mu-post-iso) _ _) (rinv x)) ∙
    ap (mu-post-ff<– id (mu x (inv x)))
      (tri-rot (ap (λ z → mu z x) (rinv x)) _ (ap (mu x) (linv x)) (rho x) (zz₁ x)))

  zz₁-rinv-suff :
    ap (λ z → mu z (inv x))
      (! (rho x) ∙ ! (ap (mu x) (linv x)) ∙ al x (inv x) x) ◃∙
    ! (al (mu x (inv x)) x (inv x)) ◃∙
    ! (ap (mu (mu x (inv x))) (rinv x)) ◃∙
    rho (mu x (inv x)) ◃∎
    =ₛ
    idp ◃∎
  zz₁-rinv-suff = {!!}
{-
  ! (lam x) ∙ ap (λ z → mu z x) (rinv x)
-}

-- morphisms of 2-groups

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  -- definition explicitly accounting for all 2-group data
  record CohGrpHomFull : Type (lmax i j) where
    constructor cohgrphomfull
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
      map-id : id == map id
      map-lam : (x : G₁) →
        ! (lam (map x))
        ==
        ! (ap map (lam x)) ∙ ! (map-comp id x) ∙ ! (ap (λ z → mu z (map x)) map-id)
      map-rho : (x : G₁) →
        ! (rho (map x))
        ==
        ! (ap map (rho x)) ∙ ! (map-comp x id) ∙ ! (ap (mu (map x)) map-id) 
      map-inv : (x : G₁) → inv (map x) == map (inv x)
      map-linv : (x : G₁) → 
        ap (λ z → mu z (map x)) (map-inv x)        
        ==
        linv (map x) ∙
        map-id ∙
        ! (ap map (linv x)) ∙
        ! (map-comp (inv x) x)
      map-rinv : (x : G₁) →
        ap (mu (map x)) (map-inv x)
        ==
        ! (rinv (map x)) ∙
        map-id ∙
        ap map (rinv x) ∙
        ! (map-comp x (inv x))

  -- shorter definition, easier to work with
  record CohGrpHom : Type (lmax i j) where
    constructor cohgrphom
    field
      map : G₁ → G₂
      map-comp : (x y : G₁) → mu (map x) (map y) == map (mu x y)
      map-id : id == map id
      map-lam : (x : G₁) →
        ! (lam (map x))
        ==
        ! (ap map (lam x)) ∙ ! (map-comp id x) ∙ ! (ap (λ z → mu z (map x)) map-id)
      map-rho : (x : G₁) →
        ! (rho (map x))
        ==
        ! (ap map (rho x)) ∙ ! (map-comp x id) ∙ ! (ap (mu (map x)) map-id)
      map-al : (x y z : G₁) →
        ! (al (map x) (map y) (map z)) ∙
        ap (mu (map x)) (map-comp y z) ∙
        map-comp x (mu y z)
        ==
        ap (λ v → mu v (map z)) (map-comp x y) ∙
        map-comp (mu x y) z ∙
        ! (ap map (al x y z))
    map-al-rot1 : (x y z : G₁) →
      ! (al (map x) (map y) (map z)) ∙
      ap (mu (map x)) (map-comp y z)
      ==
      (ap (λ v → mu v (map z)) (map-comp x y) ∙
      map-comp (mu x y) z ∙
      ! (ap map (al x y z))) ∙
      ! (map-comp x (mu y z))
    map-al-rot1 x y z = 
      ∙-assoc2-!-inv-r
        (! (al (map x) (map y) (map z)))
        (ap (mu (map x)) (map-comp y z))
        (map-comp x (mu y z)) ∙
      ap (λ q → q ∙ ! (map-comp x (mu y z))) (map-al x y z)
    map-al-rot2 : (x y z : G₁) →
      ! (al (map x) (map y) (map z))
      ==
      ap (λ v → mu v (map z)) (map-comp x y) ∙
      map-comp (mu x y) z ∙
      ! (ap map (al x y z)) ∙
      ! (map-comp x (mu y z)) ∙
      ! (ap (mu (map x)) (map-comp y z))
    map-al-rot2 x y z = 
      ! (∙-assoc (! (al (map x) (map y) (map z))) _ _ ∙
      ap (λ q → ! (al (map x) (map y) (map z)) ∙ q)
        (!-inv-r (ap (mu (map x)) (map-comp y z) ∙ map-comp x (mu y z))) ∙
      ∙-unit-r _) ∙
      ap (λ q → q ∙ ! (ap (mu (map x)) (map-comp y z) ∙ map-comp x (mu y z)))
        (map-al x y z) ∙
      ∙-assoc-!-! (ap (λ v → mu v (map z)) (map-comp x y))
        (map-comp (mu x y) z) _ _ (map-comp x (mu y z))

  -- natural isomorphisms between 2-group morphisms

  open CohGrpHom

  record CohGrpNatIso (μ₁ μ₂ : CohGrpHom) : Type (lmax i j) where
    constructor cohgrpnatiso
    field
      θ : map μ₁ ∼ map μ₂
      θ-id : map-id μ₁ ∙ θ id == map-id μ₂
      θ-comp : (x y : G₁) →
        ap2 mu (θ x) (θ y) ∙ map-comp μ₂ x y == map-comp μ₁ x y ∙ θ (mu x y)

-- some ad-hoc lemmas for algebraic reasoning below

private

  module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
    (g : B → C) (f : A → B) (mu₁ : B → B → B) (mu₂ : C → C → C)
    (x : A) where

    abstract
      aux-red0 : {x₁ x₂ : A} (p₁ : x₁ == x₂) {y₁ y₂ : B} (p₃ : y₁ == y₂)
        (p₂ : mu₁ y₂ (f x) == f x₁) {v : C} (p₄ : v == g y₁)
        (p₅ : mu₂ (g y₁) (g (f x)) == g (mu₁ y₁ (f x))) → 
        ! (ap (g ∘ f) p₁) ∙
        ! ((! (ap (λ z → mu₂ (g z) (g (f x))) p₃) ∙
          p₅ ∙
          ap (λ z → g (mu₁ z (f x))) p₃) ∙
          ap g p₂) ∙
        ! (ap (λ z → mu₂ z ((g ∘ f) x))
          (p₄ ∙ ap g p₃))
        ==
        ap g (
          ! (ap f p₁) ∙
          ! p₂ ∙
          ! (ap (λ z → mu₁ z (f x)) p₃)) ∙
        ! p₅ ∙
        ! (ap (λ z → mu₂ z (g (f x))) p₄)
      aux-red0 idp idp p₂ idp p₅ = lemma p₂ p₅
        where
          lemma : {b₁ b₂ : B} (q₁ : b₁ == b₂) {c : C} (q₂ : c == g b₁)
            → ! ((q₂ ∙ idp) ∙ ap g q₁) ∙ idp == ap g (! q₁ ∙ idp) ∙ ! q₂ ∙ idp
          lemma idp idp = idp

  module _ {i j} {A : Type i} {B : Type j} (f g : A → B) where

    abstract
      aux-red1 : {x₁ x₂ : A} {y : B} (p₁ : g x₂ == y) (p₂ : x₁ == x₂)
        (p₃ : f x₁ == g x₁) →
        (! p₁ ∙ ! (ap g p₂)) ∙ ! p₃ ∙ ap f p₂ ∙
        (ap f (! p₂) ∙ p₃ ∙ ! (ap g (! p₂))) ∙ p₁
        ==
        idp
      aux-red1 idp idp p₃ =
        ap (λ q → ! p₃ ∙ q) (∙-unit-r (p₃ ∙ idp) ∙ ∙-unit-r p₃) ∙ !-inv-l p₃

  module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
    (h₁ : B → B) (h₂ : A → A) (k₁ : C → A) (k₂ : A → B) where

    abstract
      aux-red2 : {x₁ x₂ x₄ : A} {y₄ x₃ : B} {z w : C} {p₃ : x₁ == x₂}
        {p₂ : h₁ (k₂ x₁) == k₂ (h₂ x₁)} {p₇ : h₁ (k₂ x₂) == k₂ (h₂ x₂)}
        {r₃ : k₁ w == x₄} {p₆ : k₂ x₄ == y₄} {r₂ : y₄ == k₂ (k₁ w)}
        (p₁ : x₃ == k₂ x₁) {p₄ : w == z} {p₅ : h₂ x₂ == k₁ z}
        (ρ₁ : p₂ ∙ ap k₂ (ap h₂ p₃) == ap h₁ (ap k₂ p₃) ∙ p₇)
        (ρ₂ : ap k₂ r₃ ∙ p₆ ∙ r₂ == idp) →  
        ((ap h₁ p₁ ∙ p₂ ∙ ap k₂ (ap h₂ p₃ ∙ p₅ ∙ ! (ap k₁ p₄) ∙ r₃)) ∙ p₆) ∙ r₂
        ==
        ap h₁ (p₁ ∙ ap k₂ p₃) ∙ (p₇ ∙ ap k₂ p₅) ∙ ! (ap (k₂ ∘ k₁) p₄)
      aux-red2 {p₃ = idp} {p₂} {r₃ = idp} {p₆ = idp} idp {p₄ = idp} {p₅} ρ₁ ρ₂ =
        ap (λ q → _ ∙ q) ρ₂ ∙
        ! (ap (λ q → (q ∙ ap k₂ _) ∙ idp) (! ρ₁) ∙ 
          ap (λ q → (q ∙ ap k₂ p₅) ∙ idp) (∙-unit-r p₂) ∙ 
          ! (ap (λ q → q ∙ idp) (∙-unit-r (p₂ ∙ ap k₂ (p₅ ∙ idp)) ∙
            ap (λ q → p₂ ∙ ap k₂ q) (∙-unit-r p₅))))

-- categorical structure on 2-groups

open CohGrpHom

module _ {i} {G : Type i} {{η : CohGrp G}} where

  idf2G : CohGrpHom {{η}} {{η}}
  map idf2G x = x
  map-comp idf2G x y = idp
  map-id idf2G = idp
  map-lam idf2G x = ! (∙-unit-r (! (ap (idf G) (lam x))) ∙ ap ! (ap-idf (lam x)))
  map-rho idf2G x =
    ! (∙-unit-r (! (ap (idf G) (rho x))) ∙ ap ! (ap-idf (rho x)))
  map-al idf2G x y z = ∙-unit-r (! (al x y z)) ∙ ap ! (! (ap-idf (al x y z)))
{-
module _{i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  -- composition of 2-group morphisms
  infixr 50 _∘2G_
  _∘2G_ : CohGrpHom {{η₂}} {{η₃}} → CohGrpHom {{η₁}} {{η₂}} → CohGrpHom {{η₁}} {{η₃}}
  map (F₂ ∘2G F₁) = map F₂ ∘ map F₁
  map-comp (F₂ ∘2G F₁) x y = map-comp F₂ (map F₁ x) (map F₁ y) ∙ ap (map F₂) (map-comp F₁ x y) 
  map-id (F₂ ∘2G F₁)= map-id F₂ ∙ ap (map F₂) (map-id F₁)
  map-lam (F₂ ∘2G F₁) x = 
    map-lam F₂ (map F₁ x) ∙
    ap2 _∙_ (!-ap (map F₂) (lam (map F₁ x))) idp ∙
    ap2 _∙_ (ap (ap (map F₂)) (map-lam F₁ x)) idp ∙
    ! (=ₛ-out lemma)
    where
      lemma :
        ! (ap (map F₂ ∘ map F₁) (lam x)) ◃∙
        ! (map-comp F₂ (map F₁ id) (map F₁ x) ∙
          ap (map F₂) (map-comp F₁ id x)) ◃∙
        ! (ap (λ z → mu z ((map F₂ ∘ map F₁) x))
          (map-id F₂ ∙ ap (map F₂) (map-id F₁))) ◃∎
          =ₛ
        ap (map F₂)
          (! (ap (map F₁) (lam x)) ∙
          ! (map-comp F₁ id x) ∙
          ! (ap (λ z → mu z (map F₁ x)) (map-id F₁))) ◃∙
        ! (map-comp F₂ id (map F₁ x)) ◃∙
        ! (ap (λ z → mu z (map F₂ (map F₁ x))) (map-id F₂)) ◃∎
      lemma =
        ! (ap (map F₂ ∘ map F₁) (lam x)) ◃∙
        ! (map-comp F₂ (map F₁ id) (map F₁ x) ∙
          ap (map F₂) (map-comp F₁ id x)) ◃∙
        ! (ap (λ z → mu z ((map F₂ ∘ map F₁) x))
          (map-id F₂ ∙ ap (map F₂) (map-id F₁))) ◃∎
          =ₛ₁⟨ 1 & 1 &
            ap ! (ap2 _∙_
              (=ₛ-out (apCommSq2◃ (λ z → map-comp F₂ z (map F₁ x))
                (map-id F₁))) idp) ⟩
        _
          =ₛ⟨ =ₛ-in (aux-red0 (map F₂) (map F₁) mu mu x (lam x) (map-id F₁) _ _ _) ⟩
        _ ∎ₛ         
  map-rho (F₂ ∘2G F₁) x = 
    map-rho F₂ (map F₁ x) ∙
    ap2 _∙_ (!-ap (map F₂) (rho (map F₁ x))) idp ∙
    ap2 _∙_ (ap (ap (map F₂)) (map-rho F₁ x)) idp ∙
    {!! (=ₛ-out lemma)
    where
      lemma :
        ! (ap (map F₂ ∘ map F₁) (lam x)) ◃∙
        ! (map-comp F₂ (map F₁ id) (map F₁ x) ∙
          ap (map F₂) (map-comp F₁ id x)) ◃∙
        ! (ap (λ z → mu z ((map F₂ ∘ map F₁) x))
          (map-id F₂ ∙ ap (map F₂) (map-id F₁))) ◃∎
          =ₛ
        ap (map F₂)
          (! (ap (map F₁) (lam x)) ∙
          ! (map-comp F₁ id x) ∙
          ! (ap (λ z → mu z (map F₁ x)) (map-id F₁))) ◃∙
        ! (map-comp F₂ id (map F₁ x)) ◃∙
        ! (ap (λ z → mu z (map F₂ (map F₁ x))) (map-id F₂)) ◃∎
      lemma0 =
        ! (ap (map F₂ ∘ map F₁) (lam x)) ◃∙
        ! (map-comp F₂ (map F₁ id) (map F₁ x) ∙
          ap (map F₂) (map-comp F₁ id x)) ◃∙
        ! (ap (λ z → mu z ((map F₂ ∘ map F₁) x))
          (map-id F₂ ∙ ap (map F₂) (map-id F₁))) ◃∎
          =ₛ₁⟨ 1 & 1 &
            ap ! (ap2 _∙_
              (=ₛ-out (apCommSq2◃ (λ z → map-comp F₂ z (map F₁ x))
                (map-id F₁))) idp) ⟩
        _
          =ₛ⟨ =ₛ-in (aux-red0 (map F₂) (map F₁) mu mu x (lam x) (map-id F₁) _ _ _) ⟩
        _ ∎ₛ!}
  map-al (F₂ ∘2G F₁) x y z =
    ! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y) ((map F₂ ∘ map F₁) z)) ∙
    ap (mu η₃ ((map F₂ ∘ map F₁) x))
      (map-comp F₂ (map F₁ y) (map F₁ z) ∙
      ap (map F₂) (map-comp F₁ y z))∙
    map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
    ap (map F₂) (map-comp F₁ x (mu η₁ y z))
      =⟨ ap (λ q →
            ! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y) ((map F₂ ∘ map F₁) z)) ∙
            q ∙
            map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
            ap (map F₂) (map-comp F₁ x (mu η₁ y z))) (
              ap-∙ (mu η₃ ((map F₂ ∘ map F₁) x))
                (map-comp F₂ (map F₁ y) (map F₁ z))
                (ap (map F₂) (map-comp F₁ y z)) ) ∙
          ∙-assoc2-∙2
            (! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y)
              ((map F₂ ∘ map F₁) z)))
            _ _
            (map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)))
            (ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
             ∙
          ap (λ q →
            q ∙
            ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp F₁ y z)) ∙
            map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
            ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
              (map-al-rot1 F₂ (map F₁ x) (map F₁ y) (map F₁ z)) ⟩
    ((ap (λ v → mu η₃ v (map F₂ (map F₁ z)))
      (map-comp F₂ (map F₁ x) (map F₁ y)) ∙
    map-comp F₂ (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
    ! (ap (map F₂) (al η₂ (map F₁ x) (map F₁ y) (map F₁ z)))) ∙
    ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)))) ∙
    ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp F₁ y z)) ∙
    map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
    ap (map F₂) (map-comp F₁ x (mu η₁ y z))
      =⟨ ap (λ q →
              ((ap (λ v → mu η₃ v (map F₂ (map F₁ z)))
                (map-comp F₂ (map F₁ x) (map F₁ y)) ∙
                map-comp F₂ (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙ q) ∙ _) ∙
                ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp F₁ y z)) ∙
                map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
                ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
            (!-ap (map F₂) (al η₂ (map F₁ x) (map F₁ y) (map F₁ z)) ∙
            ap (ap (map F₂)) (map-al-rot2 F₁ x y z)) ⟩
    aux-red2 (λ v → mu η₃ v (map F₂ (map F₁ z)))
      (λ v → mu η₂ v (map F₁ z)) (map F₁) (map F₂)
      (map-comp F₂ (map F₁ x) (map F₁ y))
      lemma1 lemma2
    where
      open CohGrp
      lemma1 :
        map-comp F₂ (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
        ap (map F₂) (ap (λ v → mu η₂ v (map F₁ z)) (map-comp F₁ x y))
        ==
        ap (λ v → mu η₃ v ((map F₂ ∘ map F₁) z))
          (ap (map F₂) (map-comp F₁ x y)) ∙
        map-comp F₂ (map F₁ (mu η₁ x y)) (map F₁ z)
      lemma1 = 
        map-comp F₂ (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
        ap (map F₂) (ap (λ v → mu η₂ v (map F₁ z)) (map-comp F₁ x y))
          =⟨ ap (λ q → map-comp F₂ (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙ q)
               (∘-ap (map F₂) (λ v → mu η₂ v (map F₁ z)) ((map-comp F₁ x y))) ⟩
        _
          =⟨ ! (=ₛ-out
                 (homotopy-naturality (λ v → mu η₃ (map F₂ v) (map F₂ (map F₁ z)))
                 (map F₂ ∘ (λ v → mu η₂ v (map F₁ z)))
                 (λ v → map-comp F₂ v (map F₁ z)) (map-comp F₁ x y))) ⟩
        ap (λ v → mu η₃ (map F₂ v) (map F₂ (map F₁ z))) (map-comp F₁ x y) ∙
        map-comp F₂ (map F₁ (mu η₁ x y)) (map F₁ z)
          =⟨ ap (λ q → q ∙ map-comp F₂ (map F₁ (mu η₁ x y)) (map F₁ z))
               (ap-∘ (λ v → mu η₃ v (map F₂ (map F₁ z))) (map F₂) (map-comp F₁ x y)) ⟩
        ap (λ v → mu η₃ v (map F₂ (map F₁ z))) (ap (map F₂) (map-comp F₁ x y)) ∙
        map-comp F₂ (map F₁ (mu η₁ x y)) (map F₁ z) =∎
      lemma2 :
        ap (map F₂) (! (map-comp F₁ x (mu η₁ y z)) ∙
          ! (ap (mu η₂ (map F₁ x)) (map-comp F₁ y z))) ∙
        ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
        ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp F₁ y z)) ∙
        map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
        ap (map F₂) (map-comp F₁ x (mu η₁ y z))
        ==
        idp
      lemma2 = 
        ap (map F₂) (! (map-comp F₁ x (mu η₁ y z)) ∙
          ! (ap (mu η₂ (map F₁ x)) (map-comp F₁ y z))) ∙
        ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
        ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp F₁ y z)) ∙
        map-comp F₂ (map F₁ x) (map F₁ (mu η₁ y z)) ∙
        ap (map F₂) (map-comp F₁ x (mu η₁ y z))
          =⟨ ap (λ q →
               ap (map F₂) (! (map-comp F₁ x (mu η₁ y z)) ∙
                 ! (ap (mu η₂ (map F₁ x)) (map-comp F₁ y z))) ∙
               ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
               ap (mu η₃ (map F₂ (map F₁ x))) (ap (map F₂) (map-comp F₁ y z)) ∙
               q ∙ ap (map F₂) (map-comp F₁ x (mu η₁ y z)))             
             (apCommSq2 _ _ (map-comp F₂ (map F₁ x)) (! (map-comp F₁ y z))) ⟩
        _
          =⟨ ap (λ q → q ∙
               ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
               ap (mu η₃ (map F₂ (map F₁ x))) (ap (map F₂) (map-comp F₁ y z)) ∙
               (ap (λ z₁ → mu η₃ (map F₂ (map F₁ x)) (map F₂ z₁))
                 (! (map-comp F₁ y z)) ∙
               map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)) ∙
               ! (ap (λ z₁ → map F₂ (mu η₂ (map F₁ x) z₁)) (! (map-comp F₁ y z)))) ∙
               ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
                 (ap-∙-!-! (map F₂) (map-comp F₁ x (mu η₁ y z))
                   (ap (mu η₂ (map F₁ x)) (map-comp F₁ y z))) ⟩
          _
            =⟨ ap2 (λ q₁ q₂ →
                 (! (ap (map F₂) (map-comp F₁ x (mu η₁ y z))) ∙ ! q₁) ∙
                 ! (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙ q₂ ∙
                 (ap (λ z₁ → mu η₃ (map F₂ (map F₁ x)) (map F₂ z₁))
                   (! (map-comp F₁ y z)) ∙
                 map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)) ∙
                 ! (ap (λ z₁ → map F₂ (mu η₂ (map F₁ x) z₁)) (! (map-comp F₁ y z)))) ∙
                 ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
               (∘-ap (map F₂) (mu η₂ (map F₁ x)) (map-comp F₁ y z))
               (∘-ap (mu η₃ (map F₂ (map F₁ x))) (map F₂) (map-comp F₁ y z)) ⟩
          _
            =⟨ aux-red1
                 (mu η₃ (map F₂ (map F₁ x)) ∘ map F₂)
                 (map F₂ ∘ (mu η₂ (map F₁ x)))
                 (ap (map F₂) (map-comp F₁ x (mu η₁ y z)))
                 (map-comp F₁ y z)
                 (map-comp F₂ (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ⟩
          idp
-}
