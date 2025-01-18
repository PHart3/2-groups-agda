{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2

module 2Magma where

-- (weak associative) 2-magma structure on a type
record WkMag {i} (X : Type i) : Type i where
  constructor cohgrp
  field
    instance {{1trunc}} : has-level 1 X
    mu : X → X → X
    al : (x y z : X) → mu x (mu y z) == mu (mu x y) z
    
open WkMag {{...}}  

module _ {i} (X : Type i) {{trX : has-level 1 X}} where

  ≃-2Mag : WkMag (X ≃ X)
  WkMag.mu ≃-2Mag f₁ f₂ = f₂ ∘e f₁
  WkMag.al ≃-2Mag _ _ _ = pair= idp (prop-has-all-paths _ _)

instance
  ≃-2Mag-instance : ∀ {i} {X : Type i} {{trX : has-level 1 X}} → WkMag (X ≃ X)
  ≃-2Mag-instance {X = X} = ≃-2Mag X

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} where

  -- (coherent) morphisms between 2-magmas
  record WkMagHomStr (map : G₁ → G₂) : Type (lmax i j) where
    constructor cohmaghomstr
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
      ! (al (map x) (map y) (map z)) ◃∎
      =ₛ
      ap (λ v → mu v (map z)) (map-comp x y) ◃∙
      map-comp (mu x y) z ◃∙
      ! (ap map (al x y z)) ◃∙
      ! (map-comp x (mu y z)) ◃∙
      ! (ap (mu (map x)) (map-comp y z)) ◃∎
    map-al-rot2 x y z =
      post-rotate-seq-in
        {r = ap (λ v → mu v (map z)) (map-comp x y) ◃∙
             map-comp (mu x y) z ◃∙
             ! (ap map (al x y z)) ◃∎}
        {q = ap (mu (map x)) (map-comp y z) ◃∙ map-comp x (mu y z) ◃∎}
        (=ₛ-in (map-al x y z))

  record WkMagHom : Type (lmax i j) where
    constructor cohmaghom
    field
      map : G₁ → G₂
      {{str}} : WkMagHomStr map
  open WkMagHom

  -- weak morphisms between 2-magmas
  record WkMagWkHom : Type (lmax i j) where
    constructor wkmaghom
    field
      map-wk : G₁ → G₂
      map-comp-wk : (x y : G₁) → mu (map-wk x) (map-wk y) == map-wk (mu x y)
  open WkMagWkHom

  maghom-forg : WkMagHom → WkMagWkHom
  map-wk (maghom-forg f) = map f
  map-comp-wk (maghom-forg f) = map-comp (str f) where open WkMagHomStr

  record WkMagNatIso (μ₁ μ₂ : WkMagWkHom) : Type (lmax i j) where
    constructor cohgrpnatiso
    field
      θ : map-wk μ₁ ∼ map-wk μ₂
      θ-comp : (x y : G₁) →
        map-comp-wk μ₂ x y == ! (ap2 mu (θ x) (θ y)) ∙ map-comp-wk μ₁ x y ∙ θ (mu x y)
  open WkMagNatIso

  natiso-id : (μ : WkMagWkHom) → WkMagNatIso μ μ
  θ (natiso-id μ) x = idp
  θ-comp (natiso-id μ) x y = ! (∙-unit-r (map-comp-wk μ x y))

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} where

  open WkMagNatIso
  open WkMagWkHom
  
  infixr 50 _natiso-∘_
  _natiso-∘_ : {μ₁ μ₂ μ₃ : WkMagWkHom {{η₁}} {{η₂}}} → WkMagNatIso μ₂ μ₃ → WkMagNatIso μ₁ μ₂ → WkMagNatIso μ₁ μ₃
  θ (F₂ natiso-∘ F₁) x = θ F₁ x ∙ θ F₂ x
  θ-comp (_natiso-∘_ {μ₁} {μ₂} {μ₃} F₂ F₁) x y = =ₛ-out $
    map-comp-wk μ₃ x y ◃∎
      =ₛ⟨ =ₛ-in (θ-comp F₂ x y) ⟩
    ! (ap2 mu (θ F₂ x) (θ F₂ y)) ◃∙
    map-comp-wk μ₂ x y ◃∙
    θ F₂(mu x y) ◃∎
      =ₑ⟨ 1 & 1 & (! (ap2 mu (θ F₁ x) (θ F₁ y)) ◃∙ map-comp-wk μ₁ x y ◃∙ θ F₁ (mu x y) ◃∎) % =ₛ-in (θ-comp F₁ x y) ⟩
    ! (ap2 mu (θ F₂ x) (θ F₂ y)) ◃∙
    ! (ap2 mu (θ F₁ x) (θ F₁ y)) ◃∙
    map-comp-wk μ₁ x y ◃∙
    θ F₁ (mu x y) ◃∙
    θ F₂ (mu x y) ◃∎
      =ₛ₁⟨ 0 & 2 & ∙-! (ap2 mu (θ F₂ x) (θ F₂ y)) (ap2 mu (θ F₁ x) (θ F₁ y)) ⟩
    ! (ap2 mu (θ F₁ x) (θ F₁ y) ∙
      ap2 mu (θ F₂ x) (θ F₂ y)) ◃∙
    map-comp-wk μ₁ x y ◃∙
    θ F₁ (mu x y) ◃∙
    θ F₂ (mu x y) ◃∎
      =ₛ₁⟨ 0 & 1 & ap ! (∙-ap2 mu (θ F₁ x) (θ F₂ x) (θ F₁ y) (θ F₂ y)) ⟩
    ! (ap2 mu (θ F₁ x ∙ θ F₂ x) (θ F₁ y ∙ θ F₂ y)) ◃∙
    map-comp-wk μ₁ x y ◃∙
    θ F₁ (mu x y) ◃∙
    θ F₂ (mu x y) ◃∎ ∎ₛ

-- some ad-hoc lemmas for algebraic reasoning below

private

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
      aux-red2 : {x₁ x₂ x₄ : A} {y₁ y₂ : B} {z₂ z₁ : C} {p₃ : x₁ == x₂}
        {p₂ : h₁ (k₂ x₁) == k₂ (h₂ x₁)} {p₇ : h₁ (k₂ x₂) == k₂ (h₂ x₂)}
        {r₂ : k₁ z₁ == x₄} {p₆ : k₂ x₄ == y₁} {r₁ : y₁ == k₂ (k₁ z₁)}
        (p₁ : y₂ == k₂ x₁) {p₄ : z₁ == z₂} {p₅ : h₂ x₂ == k₁ z₂}
        (ρ₁ : p₂ ∙ ap k₂ (ap h₂ p₃) == ap h₁ (ap k₂ p₃) ∙ p₇)
        (ρ₂ : ap k₂ r₂ ∙ p₆ ∙ r₁ == idp) →  
        ((ap h₁ p₁ ∙ p₂ ∙ ap k₂ (ap h₂ p₃ ∙ p₅ ∙ ! (ap k₁ p₄) ∙ r₂)) ∙ p₆) ∙ r₁
          ==
        ap h₁ (p₁ ∙ ap k₂ p₃) ∙ (p₇ ∙ ap k₂ p₅) ∙ ! (ap (k₂ ∘ k₁) p₄)
      aux-red2 {p₃ = idp} {p₂} {r₂ = idp} {p₆ = idp} idp {p₄ = idp} {p₅} ρ₁ ρ₂ =
        ap (λ q → _ ∙ q) ρ₂ ∙
        ! (ap (λ q → (q ∙ ap k₂ _) ∙ idp) (! ρ₁) ∙ 
          ap (λ q → (q ∙ ap k₂ p₅) ∙ idp) (∙-unit-r p₂) ∙ 
          ! (ap (λ q → q ∙ idp) (∙-unit-r (p₂ ∙ ap k₂ (p₅ ∙ idp)) ∙
            ap (λ q → p₂ ∙ ap k₂ q) (∙-unit-r p₅))))

open WkMagWkHom public

module _ {i} {G : Type i} {{η : WkMag G}} where

  idf2Mw : WkMagWkHom {{η}} {{η}}
  map-wk idf2Mw = idf G
  map-comp-wk idf2Mw x y = idp

  open WkMagHomStr

  idf2M : WkMagHomStr (idf G)
  map-comp idf2M x y = idp
  map-al idf2M x y z = ∙-unit-r (! (al x y z)) ∙ ap ! (! (ap-idf (al x y z)))

module _{i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} {{η₃ : WkMag G₃}} where

  open WkMagHom
  open WkMagHomStr {{...}}

  -- composition of 2-magma morphisms
  
  infixr 60 _∘2Mσ_
  _∘2Mσ_ :  (F₂ : WkMagHom {{η₂}} {{η₃}}) (F₁ : WkMagHom {{η₁}} {{η₂}}) → WkMagHomStr (map F₂ ∘ map F₁)
  WkMagHomStr.map-comp (F₂ ∘2Mσ F₁) x y = map-comp (map F₁ x) (map F₁ y) ∙ ap (map F₂) (map-comp x y) 
  WkMagHomStr.map-al (F₂ ∘2Mσ F₁) x y z =
    ! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y) ((map F₂ ∘ map F₁) z)) ∙
    ap (mu η₃ ((map F₂ ∘ map F₁) x))
      (map-comp (map F₁ y) (map F₁ z) ∙
      ap (map F₂) (map-comp y z))∙
    map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
    ap (map F₂) (map-comp x (mu η₁ y z))
      =⟨ ap (λ q →
            ! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y) ((map F₂ ∘ map F₁) z)) ∙
            q ∙
            map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
            ap (map F₂) (map-comp x (mu η₁ y z))) (
              ap-∙ (mu η₃ ((map F₂ ∘ map F₁) x))
                (map-comp (map F₁ y) (map F₁ z))
                (ap (map F₂) (map-comp y z)) ) ∙
          ∙-assoc2-∙2
            (! (al η₃ ((map F₂ ∘ map F₁) x) ((map F₂ ∘ map F₁) y)
              ((map F₂ ∘ map F₁) z)))
            _ _
            (map-comp (map F₁ x) (map F₁ (mu η₁ y z)))
            (ap (map F₂) (map-comp x (mu η₁ y z)))
             ∙
          ap (λ q →
            q ∙
            ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp y z)) ∙
            map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
            ap (map F₂) (map-comp x (mu η₁ y z)))
              (map-al-rot1 (map F₁ x) (map F₁ y) (map F₁ z)) ⟩
    ((ap (λ v → mu η₃ v (map F₂ (map F₁ z)))
      (map-comp (map F₁ x) (map F₁ y)) ∙
    map-comp (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
    ! (ap (map F₂) (al η₂ (map F₁ x) (map F₁ y) (map F₁ z)))) ∙
    ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)))) ∙
    ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp y z)) ∙
    map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
    ap (map F₂) (map-comp x (mu η₁ y z))
      =⟨ ap (λ q →
              ((ap (λ v → mu η₃ v (map F₂ (map F₁ z)))
                (map-comp (map F₁ x) (map F₁ y)) ∙
                map-comp (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙ q) ∙ _) ∙
                ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp y z)) ∙
                map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
                ap (map F₂) (map-comp x (mu η₁ y z)))
            (!-ap (map F₂) (al η₂ (map F₁ x) (map F₁ y) (map F₁ z)) ∙
            ap (ap (map F₂)) (=ₛ-out (map-al-rot2 x y z))) ⟩
    aux-red2 (λ v → mu η₃ v (map F₂ (map F₁ z)))
      (λ v → mu η₂ v (map F₁ z)) (map F₁) (map F₂)
      (map-comp (map F₁ x) (map F₁ y))
      lemma1 lemma2
    where
      open WkMag
      lemma1 :
        map-comp (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
        ap (map F₂) (ap (λ v → mu η₂ v (map F₁ z)) (map-comp x y))
          ==
        ap (λ v → mu η₃ v ((map F₂ ∘ map F₁) z))
          (ap (map F₂) (map-comp x y)) ∙
        map-comp (map F₁ (mu η₁ x y)) (map F₁ z)
      lemma1 = 
        map-comp (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙
        ap (map F₂) (ap (λ v → mu η₂ v (map F₁ z)) (map-comp x y))
          =⟨ ap (λ q → map-comp (mu η₂ (map F₁ x) (map F₁ y)) (map F₁ z) ∙ q)
               (∘-ap (map F₂) (λ v → mu η₂ v (map F₁ z)) ((map-comp x y))) ⟩
        _
          =⟨ ! (=ₛ-out
                 (homotopy-naturality (λ v → mu η₃ (map F₂ v) (map F₂ (map F₁ z)))
                 (map F₂ ∘ (λ v → mu η₂ v (map F₁ z)))
                 (λ v → map-comp v (map F₁ z)) (map-comp x y))) ⟩
        ap (λ v → mu η₃ (map F₂ v) (map F₂ (map F₁ z))) (map-comp x y) ∙
        map-comp (map F₁ (mu η₁ x y)) (map F₁ z)
          =⟨ ap (λ q → q ∙ map-comp (map F₁ (mu η₁ x y)) (map F₁ z))
               (ap-∘ (λ v → mu η₃ v (map F₂ (map F₁ z))) (map F₂) (map-comp x y)) ⟩
        ap (λ v → mu η₃ v (map F₂ (map F₁ z))) (ap (map F₂) (map-comp x y)) ∙
        map-comp (map F₁ (mu η₁ x y)) (map F₁ z) =∎
      lemma2 :
        ap (map F₂) (! (map-comp x (mu η₁ y z)) ∙
          ! (ap (mu η₂ (map F₁ x)) (map-comp y z))) ∙
        ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
        ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp y z)) ∙
        map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
        ap (map F₂) (map-comp x (mu η₁ y z))
          ==
        idp
      lemma2 = 
        ap (map F₂) (! (map-comp x (mu η₁ y z)) ∙
          ! (ap (mu η₂ (map F₁ x)) (map-comp y z))) ∙
        ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
        ap (mu η₃ ((map F₂ ∘ map F₁) x)) (ap (map F₂) (map-comp y z)) ∙
        map-comp (map F₁ x) (map F₁ (mu η₁ y z)) ∙
        ap (map F₂) (map-comp x (mu η₁ y z))
          =⟨ ap (λ q →
               ap (map F₂) (! (map-comp x (mu η₁ y z)) ∙
                 ! (ap (mu η₂ (map F₁ x)) (map-comp y z))) ∙
               ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
               ap (mu η₃ (map F₂ (map F₁ x))) (ap (map F₂) (map-comp y z)) ∙
               q ∙ ap (map F₂) (map-comp x (mu η₁ y z)))             
             (apCommSq2 _ _ (map-comp (map F₁ x)) (! (map-comp y z))) ⟩
        _
          =⟨ ap (λ q → q ∙
               ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙
               ap (mu η₃ (map F₂ (map F₁ x))) (ap (map F₂) (map-comp y z)) ∙
               (ap (λ z₁ → mu η₃ (map F₂ (map F₁ x)) (map F₂ z₁))
                 (! (map-comp y z)) ∙
               map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)) ∙
               ! (ap (λ z₁ → map F₂ (mu η₂ (map F₁ x) z₁)) (! (map-comp y z)))) ∙
               ap (map F₂) (map-comp x (mu η₁ y z)))
                 (ap-∙-!-! (map F₂) (map-comp x (mu η₁ y z))
                   (ap (mu η₂ (map F₁ x)) (map-comp y z))) ⟩
          _
            =⟨ ap2 (λ q₁ q₂ →
                 (! (ap (map F₂) (map-comp x (mu η₁ y z))) ∙ ! q₁) ∙
                 ! (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ∙ q₂ ∙
                 (ap (λ z₁ → mu η₃ (map F₂ (map F₁ x)) (map F₂ z₁))
                   (! (map-comp y z)) ∙
                 map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z)) ∙
                 ! (ap (λ z₁ → map F₂ (mu η₂ (map F₁ x) z₁)) (! (map-comp y z)))) ∙
                 ap (map F₂) (map-comp x (mu η₁ y z)))
               (∘-ap (map F₂) (mu η₂ (map F₁ x)) (map-comp y z))
               (∘-ap (mu η₃ (map F₂ (map F₁ x))) (map F₂) (map-comp y z)) ⟩
          _
            =⟨ aux-red1
                 (mu η₃ (map F₂ (map F₁ x)) ∘ map F₂)
                 (map F₂ ∘ (mu η₂ (map F₁ x)))
                 (ap (map F₂) (map-comp x (mu η₁ y z)))
                 (map-comp y z)
                 (map-comp (map F₁ x) (mu η₂ (map F₁ y) (map F₁ z))) ⟩
          idp
          
  infixr 50 _∘2M_
  _∘2M_ : WkMagHom {{η₂}} {{η₃}} → WkMagHom {{η₁}} {{η₂}} → WkMagHom {{η₁}} {{η₃}}
  map (F₂ ∘2M F₁) = map F₂ ∘ map F₁
  str (F₂ ∘2M F₁) = F₂ ∘2Mσ F₁

  infixr 50 _∘2Mw_
  _∘2Mw_ : WkMagWkHom {{η₂}} {{η₃}} → WkMagWkHom {{η₁}} {{η₂}} → WkMagWkHom {{η₁}} {{η₃}}
  map-wk (F₂ ∘2Mw F₁) = map-wk F₂ ∘ map-wk F₁
  map-comp-wk (F₂ ∘2Mw F₁) x y = map-comp-wk F₂ (map-wk F₁ x) (map-wk F₁ y) ∙ ap (map-wk F₂) (map-comp-wk F₁ x y)
