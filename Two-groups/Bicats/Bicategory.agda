{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module Bicategory where

module _ (j : ULevel) where

  -- Nota bene: We define a bicategory as a (2,1)-category with paths as 2-cells.
  record BicatStr {i} (B₀ : Type i) : Type (lmax i (lsucc j)) where
    constructor bicatstr
    infixr 82 _◻_
    field
      hom : B₀ → B₀ → Type j
      id₁ : (a : B₀) → hom a a
      _◻_ : {a b c : B₀} → hom b c → hom a b → hom a c
      ρ : {a b : B₀} (f : hom a b) → f == f ◻ id₁ a
      lamb : {a b : B₀} (f : hom a b) → f == id₁ b ◻ f
      α : {a b c d : B₀} (h : hom c d) (g : hom b c) (f : hom a b) → h ◻ g ◻ f == (h ◻ g) ◻ f
      id₁-r : {a b : B₀} {f g : hom a b} (θ : g == f) →  ρ g ∙ ap (λ m → m ◻ id₁ a) θ == θ ∙ ρ f  
      id₁-l : {a b : B₀} {f g : hom a b} (θ : g == f) →  lamb g ∙ ap (λ m → id₁ b ◻ m) θ == θ ∙ lamb f
      α-law1 : {a b c d : B₀} (f : hom a b) (g : hom b c) {h i : hom c d} (θ : h == i)
        → α h g f ∙ ap (λ m → m ◻ f) (ap (λ m → m ◻ g) θ) == ap (λ m → m ◻ (g ◻ f)) θ ∙ α i g f
      α-law2 : {a b c d : B₀} (f : hom a b) {g h : hom b c} {i : hom c d} (θ : g == h)
        → α i g f ∙ ap (λ m → m ◻ f) (ap (λ m → i ◻ m) θ) == ap (λ m → i ◻ m) (ap (λ m → m ◻ f) θ) ∙ α i h f
      α-law3 : {a b c d : B₀} {f g : hom a b} (h : hom b c) (i : hom c d) (θ : f == g)
        → α i h f ∙ ap (λ m → (i ◻ h) ◻ m) θ == ap (λ m → i ◻ m) (ap (λ m → h ◻ m) θ) ∙ α i h g 
      tri-bc : {a b c : B₀} (f : hom a b) (g : hom b c)
        → ap (λ m → g ◻ m) (lamb f) ∙ α g (id₁ b) f == ap (λ m → m ◻ f) (ρ g)
      pent-bc : {a b c d e : B₀} (f : hom a b) (g : hom b c) (h : hom c d) (i : hom d e)
        →  α i h (g ◻ f) ∙ α (i ◻ h) g f == ap (λ m → i ◻ m) (α h g f) ∙ α i (h ◻ g) f ∙ ap (λ m → m ◻ f) (α i h g)
      instance {{hom-trunc}} : {a b : B₀} → has-level 1 (hom a b)

open BicatStr {{...}}

module _ {i j} {B₀ : Type i} where

  infixr 82 ⟦_⟧_◻_
  ⟦_⟧_◻_ : (ξ : BicatStr j B₀) {a b c : B₀} → hom {{ξ}} b c → hom {{ξ}} a b → hom {{ξ}} a c
  ⟦_⟧_◻_ ξ g f = _◻_ {{ξ}} g f 

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- pseudofunctors
  record PsfunctorStr (F₀ : B₀ → C₀) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor psfunctorstr
    field
      F₁ : {a b : B₀} → hom a b → hom (F₀ a) (F₀ b)
      F-id₁ : (a : B₀) → F₁ (id₁ a) == id₁ (F₀ a)
      F-◻ : {a b c : B₀} (f : hom a b) (g : hom b c)
        → F₁ (⟦ ξB ⟧ g ◻ f) == ⟦ ξC ⟧ F₁ g ◻ F₁ f  -- somehow Agda gets stuck on the two instance candidates (make GitHub issue)
      F-ρ : {a b : B₀} (f : hom a b) → ρ (F₁ f) == ap F₁ (ρ f) ∙ F-◻ (id₁ a) f ∙ ap (λ m → F₁ f ◻ m) (F-id₁ a)
      F-λ : {a b : B₀} (f : hom a b) → lamb (F₁ f) == ap F₁ (lamb f) ∙ F-◻ f (id₁ b) ∙ ap (λ m → m ◻ F₁ f) (F-id₁ b)
      F-α : {a b c d : B₀} (h : hom c d) (g : hom b c) (f : hom a b)
        →
        α (F₁ h) (F₁ g) (F₁ f)
          ==
        ! (ap (λ m → F₁ h ◻ m) (F-◻ f g)) ∙
        ! (F-◻ (⟦ ξB ⟧ g ◻ f) h) ∙
        ap F₁ (α h g f) ∙
        F-◻ f (⟦ ξB ⟧ h ◻ g) ∙
        ap (λ m → m ◻ F₁ f) (F-◻ g h)
        
    -- hnat properties of F-◻
    F-◻-nat-l : {a b c : B₀} {m₁ m₂ : hom a b} (m₃ : hom b c) (q : m₁ == m₂)
      → F-◻ m₁ m₃ == ap (λ m → F₁ (⟦ ξB ⟧ m₃ ◻ m)) q ∙ F-◻ m₂ m₃ ∙' ! (ap (λ m → ⟦ ξC ⟧ F₁ m₃ ◻ F₁ m) q)
    F-◻-nat-l m₃ q = apCommSq2-∙' (λ m → F-◻ m m₃) q
    F-◻-nat-r : {a b c : B₀} (m₁ : hom a b) {m₂ m₃ : hom b c} (q : m₂ == m₃)
      → F-◻ m₁ m₂ == ap (λ m → F₁ (⟦ ξB ⟧ m ◻ m₁)) q ∙ F-◻ m₁ m₃ ∙' ! (ap (λ m → ⟦ ξC ⟧ F₁ m ◻ F₁ m₁) q)
    F-◻-nat-r m₁ q = apCommSq2-∙' (F-◻ m₁) q

  record Psfunctor : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor psfunctor
    field
      map-pf : B₀ → C₀
      {{str-pf}} : PsfunctorStr map-pf
      
module _ {i j} {B₀ : Type i} {{ξ : BicatStr j B₀}} where

  open PsfunctorStr
  
  -- identity pseudofunctor
  idfBC : PsfunctorStr (idf B₀)
  F₁ idfBC = λ f → f
  F-id₁ idfBC = λ a → idp
  F-◻ idfBC = λ f g → idp
  F-ρ idfBC = λ f → ! (∙-unit-r (ap (λ z → z) (ρ f)) ∙ ap-idf (ρ f))
  F-λ idfBC = λ f → ! (∙-unit-r (ap (λ z → z) (lamb f)) ∙ ap-idf (lamb f))
  F-α idfBC = λ h g f → ! (∙-unit-r (ap (λ z → z) (α h g f)) ∙ ap-idf (α h g f))

module _ {i₁ i₂ i₃ j₁ j₂ j₃} {B₀ : Type i₁} {C₀ : Type i₂} {D₀ : Type i₃}
  {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} {{ξD : BicatStr j₃ D₀}} where

  open PsfunctorStr
  open Psfunctor

  -- composition of pseudofunctors  
  infixr 60 _∘BCσ_
  _∘BCσ_ :  (φ₂ : Psfunctor {{ξC}} {{ξD}}) (φ₁ : Psfunctor {{ξB}} {{ξC}}) → PsfunctorStr (map-pf φ₂ ∘ map-pf φ₁)
  PsfunctorStr.F₁ (φ₂ ∘BCσ φ₁) = F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)
  PsfunctorStr.F-id₁ (φ₂ ∘BCσ φ₁) a = ap (F₁ (str-pf φ₂)) (F-id₁ (str-pf φ₁) a) ∙ F-id₁ (str-pf φ₂) (map-pf φ₁ a)
  PsfunctorStr.F-◻ (φ₂ ∘BCσ φ₁) f g = ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f g) ∙ F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g)
  PsfunctorStr.F-ρ (φ₂ ∘BCσ φ₁) {a} {b} f =
    F-ρ (str-pf φ₂) (F₁ (str-pf φ₁) f) ∙
    ap
      (λ q →
        ap (F₁ (str-pf φ₂)) q ∙
        F-◻ (str-pf φ₂) (id₁ (map-pf φ₁ a)) (F₁ (str-pf φ₁) f) ∙
        ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f) ◻ m) (F-id₁ (str-pf φ₂) (map-pf φ₁ a)))
      (F-ρ (str-pf φ₁) f) ∙
    ! (ap
        (λ q →
          ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) (ρ f) ∙
          (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) (id₁ a) f) ∙ q) ∙
          ap (λ m → (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) f ◻ m)
            (ap (F₁ (str-pf φ₂)) (F-id₁ (str-pf φ₁) a) ∙ F-id₁ (str-pf φ₂) (map-pf φ₁ a)))
        (F-◻-nat-l (str-pf φ₂) (F₁ (str-pf φ₁) f) (F-id₁ (str-pf φ₁) a)) ∙
      lemma-ρ (ρ f) (F-◻ (str-pf φ₁) (id₁ a) f) (F-id₁ (str-pf φ₁) a)
        (F-id₁ (str-pf φ₁) a) (F-id₁ (str-pf φ₂) (map-pf φ₁ a))
        (F-◻ (str-pf φ₂) (id₁ (map-pf φ₁ a)) (F₁ (str-pf φ₁) f)))
    where abstract
      lemma-ρ : {x : B₀} {g₁ g₂ : hom x b} (p₁ : g₁ == g₂)
        {k₁ k₂ k₃ k₄ : hom (map-pf φ₁ x) (map-pf φ₁ a)}
        (p₂ : F₁ (str-pf φ₁) g₂ == F₁ (str-pf φ₁) f ◻ k₁)
        (p₃ : k₁ == k₂) (p₅ : k₃ == k₄)
        {v : hom (map-pf φ₂ (map-pf φ₁ x)) (map-pf φ₂ (map-pf φ₁ a))}
        (p₆ : F₁ (str-pf φ₂) k₄ == v) (p₄ : _)  
        → 
        ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) p₁ ∙
        (ap (F₁ (str-pf φ₂)) p₂ ∙
        ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f ◻ m)) p₃ ∙ p₄ ∙'
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f) ◻ F₁ (str-pf φ₂) m) p₅)) ∙
        ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f) ◻ m)
          (ap (F₁ (str-pf φ₂)) p₅ ∙ p₆)
          ==
        ap (F₁ (str-pf φ₂))
          (ap (F₁ (str-pf φ₁)) p₁ ∙ p₂ ∙ ap (λ m → F₁ (str-pf φ₁) f ◻ m) p₃) ∙ p₄ ∙
        ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f) ◻ m) p₆
      lemma-ρ idp p₂ idp idp idp p₄ = aux-ρ (F₁ (str-pf φ₂)) p₂ p₄
        where
          aux-ρ : ∀ {i j} {A : Type i} {B : Type j} (g : A → B)
            {x₁ x₂ : A} (q₁ : x₁ == x₂) {b : B} (q₂ : g x₂ == b)
            → (ap g q₁ ∙ q₂) ∙ idp == ap g (q₁ ∙ idp) ∙ q₂ ∙ idp
          aux-ρ _ idp idp = idp
  PsfunctorStr.F-λ (φ₂ ∘BCσ φ₁) {a} {b} f =
    F-λ (str-pf φ₂) (F₁ (str-pf φ₁) f) ∙
    ap
      (λ q →
        ap (F₁ (str-pf φ₂)) q ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (id₁ (map-pf φ₁ b)) ∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (F-id₁ (str-pf φ₂) (map-pf φ₁ b)))
      (F-λ (str-pf φ₁) f) ∙
    ! (ap
        (λ q →
          ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) (lamb f) ∙
          (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f (id₁ b)) ∙ q) ∙
          ap (λ m → m ◻ (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) f)
            (ap (F₁ (str-pf φ₂)) (F-id₁ (str-pf φ₁) b) ∙ F-id₁ (str-pf φ₂) (map-pf φ₁ b)))
        (F-◻-nat-r (str-pf φ₂) (F₁ (str-pf φ₁) f) (F-id₁ (str-pf φ₁) b)) ∙
      lemma-λ (lamb f) (F-id₁ (str-pf φ₁) b) (F-id₁ (str-pf φ₁) b)
        (F-◻ (str-pf φ₁) f (id₁ b)) (F-id₁ (str-pf φ₂) (map-pf φ₁ b))
        (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (id₁ (map-pf φ₁ b))))
    where abstract
      lemma-λ : {x : B₀} {g₁ g₂ : hom a x} (p₁ : g₁ == g₂)
        {k₁ k₂ k₃ k₄ : hom (map-pf φ₁ b) (map-pf φ₁ x)}
        (p₃ : k₁ == k₂) (p₅ : k₃ == k₄)
        (p₂ : F₁ (str-pf φ₁) g₂ == k₁ ◻ F₁ (str-pf φ₁) f)
        {t : hom (map-pf φ₂ (map-pf φ₁ b)) (map-pf φ₂ (map-pf φ₁ x))}
        (p₆ : F₁ (str-pf φ₂) k₄ == t) (p₄ : _)  
        → 
        ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) p₁ ∙
        (ap (F₁ (str-pf φ₂)) p₂ ∙
        ap (λ m → F₁ (str-pf φ₂) (m ◻ F₁ (str-pf φ₁) f)) p₃ ∙ p₄ ∙'
        ! (ap (λ m → F₁ (str-pf φ₂) m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) p₅)) ∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f))
          (ap (F₁ (str-pf φ₂)) p₅ ∙ p₆)
          ==
        ap (F₁ (str-pf φ₂))
          (ap (F₁ (str-pf φ₁)) p₁ ∙ p₂ ∙ ap (λ m → m ◻ F₁ (str-pf φ₁) f) p₃) ∙ p₄ ∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) p₆
      lemma-λ idp idp idp p₂ idp p₄ = aux-λ (F₁ (str-pf φ₂)) p₂ p₄
        where
          aux-λ : ∀ {i j} {A : Type i} {B : Type j} (g : A → B)
            {x₁ x₂ : A} (q₁ : x₁ == x₂) {b : B} (q₂ : g x₂ == b)
            → (ap g q₁ ∙ q₂) ∙ idp == ap g (q₁ ∙ idp) ∙ q₂ ∙ idp
          aux-λ _ idp idp = idp
  PsfunctorStr.F-α (φ₂ ∘BCσ φ₁) {a} {b} {c} {d} h g f = 
    F-α (str-pf φ₂) (F₁ (str-pf φ₁) h) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) f) ∙
    ap
      (λ q →
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ∙
        ! (F-◻ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) g ◻ F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) h)) ∙
        ap (F₁ (str-pf φ₂)) q ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ F₁ (str-pf φ₁) g) ∙
        ap (λ m → m ◻ (F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f))) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)))
      (F-α (str-pf φ₁) h g f) ∙
    =ₛ-out lemma-α
    where abstract
      lemma-α :
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (F-◻ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) g ◻ F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) h)) ◃∙
        ap (F₁ (str-pf φ₂))
          (! (ap (λ m → F₁ (str-pf φ₁) h ◻ m) (F-◻ (str-pf φ₁) f g)) ∙
          ! (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          ap (F₁ (str-pf φ₁)) (α h g f) ∙
          F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g) ∙
          ap (λ m → m ◻ F₁ (str-pf φ₁) f) (F-◻ (str-pf φ₁) g h)) ◃∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ F₁ (str-pf φ₁) g) ◃∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎
          =ₛ
        ! (ap (λ m → (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) h ◻ m)
            (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f g) ∙
            F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f)) (F₁ (str-pf φ₁) h)) ◃∙
        ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) (α h g f) ◃∙
        (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g)) ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) (⟦ ξB ⟧ h ◻ g))) ◃∙
        ap (λ m → m ◻ (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) f)
          (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) g h) ∙
          F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎
      lemma-α =
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (F-◻ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) g ◻ F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) h)) ◃∙  -- here
        ap (F₁ (str-pf φ₂))
          (! (ap (λ m → F₁ (str-pf φ₁) h ◻ m) (F-◻ (str-pf φ₁) f g)) ∙
          ! (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          ap (F₁ (str-pf φ₁)) (α h g f) ∙
          F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g) ∙
          ap (λ m → m ◻ F₁ (str-pf φ₁) f) (F-◻ (str-pf φ₁) g h)) ◃∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ F₁ (str-pf φ₁) g) ◃∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎
          =ₛ₁⟨ 3 & 1 & F-◻-nat-r (str-pf φ₂) (F₁ (str-pf φ₁) f) (! (F-◻ (str-pf φ₁) g h)) ⟩
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (F-◻ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) g ◻ F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) h)) ◃∙
        ap (F₁ (str-pf φ₂))
          (! (ap (λ m → F₁ (str-pf φ₁) h ◻ m) (F-◻ (str-pf φ₁) f g)) ∙
          ! (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          ap (F₁ (str-pf φ₁)) (α h g f) ∙
          F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g) ∙
          ap (λ m → m ◻ F₁ (str-pf φ₁) f) (F-◻ (str-pf φ₁) g h)) ◃∙
        (ap (λ m → F₁ (str-pf φ₂) (⟦ ξC ⟧ m ◻ F₁ (str-pf φ₁) f)) (! (F-◻ (str-pf φ₁) g h)) ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) (⟦ ξB ⟧ h ◻ g)) ∙'
        ! (ap (λ m → ⟦ ξD ⟧ F₁ (str-pf φ₂) m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (! (F-◻ (str-pf φ₁) g h)))) ◃∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎
          =ₛ₁⟨ 1 & 1 & ap ! (F-◻-nat-l (str-pf φ₂) (F₁ (str-pf φ₁) h) (! (F-◻ (str-pf φ₁) f g))) ⟩
        ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (ap (λ m → F₁ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ m)) (! (F-◻ (str-pf φ₁) f g)) ∙
          F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f)) (F₁ (str-pf φ₁) h) ∙'
          ! (ap (λ m → ⟦ ξD ⟧ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ F₁ (str-pf φ₂) m) (! (F-◻ (str-pf φ₁) f g)))) ◃∙
        ap (F₁ (str-pf φ₂))
          (! (ap (λ m → F₁ (str-pf φ₁) h ◻ m) (F-◻ (str-pf φ₁) f g)) ∙
          ! (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          ap (F₁ (str-pf φ₁)) (α h g f) ∙
          F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g) ∙
          ap (λ m → m ◻ F₁ (str-pf φ₁) f) (F-◻ (str-pf φ₁) g h)) ◃∙
        (ap (λ m → F₁ (str-pf φ₂) (⟦ ξC ⟧ m ◻ F₁ (str-pf φ₁) f)) (! (F-◻ (str-pf φ₁) g h)) ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) (⟦ ξB ⟧ h ◻ g)) ∙'
        ! (ap (λ m → ⟦ ξD ⟧ F₁ (str-pf φ₂) m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (! (F-◻ (str-pf φ₁) g h)))) ◃∙
        ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎
          =ₛ⟨ =ₛ-in $
                aux-α
                  (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))
                  (F-◻ (str-pf φ₁) f g)
                  (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f)) (F₁ (str-pf φ₁) h))
                  (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h)
                  (α h g f)
                  (F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g))
                  (F-◻ (str-pf φ₁) g h)
                  (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) (⟦ ξB ⟧ h ◻ g)))
                  (F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ⟩
        ! (ap (λ m → (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) h ◻ m)
            (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f g) ∙
            F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) g))) ◃∙
        ! (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f) h) ∙
          F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) (⟦ ξB ⟧ g ◻ f)) (F₁ (str-pf φ₁) h)) ◃∙
        ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) (α h g f) ◃∙
        (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) f (⟦ ξB ⟧ h ◻ g)) ∙
        F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) f) (F₁ (str-pf φ₁) (⟦ ξB ⟧ h ◻ g))) ◃∙
        ap (λ m → m ◻ (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) f)
          (ap (F₁ (str-pf φ₂)) (F-◻ (str-pf φ₁) g h) ∙
          F-◻ (str-pf φ₂) (F₁ (str-pf φ₁) g) (F₁ (str-pf φ₁) h)) ◃∎ ∎ₛ
        where
          aux-α :
            {k₁ : hom (map-pf φ₂ (map-pf φ₁ a)) (map-pf φ₂ (map-pf φ₁ c))}
            {h₁ h₂ : hom (map-pf φ₁ a) (map-pf φ₁ c)}
            {h₆ h₇ : hom (map-pf φ₁ b) (map-pf φ₁ d)}
            {g₁ g₂ : hom a d}
            {k₅ : hom (map-pf φ₂ (map-pf φ₁ b)) (map-pf φ₂ (map-pf φ₁ d))}
            (p₁ : F₁ (str-pf φ₂) h₂ == k₁) (p₂ : h₁ == h₂)
            (p₃ : F₁ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ h₁) == F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ F₁ (str-pf φ₂) h₁)
            (p₄ : F₁ (str-pf φ₁) g₁ == F₁ (str-pf φ₁) h ◻ h₁)
            (p₅ : g₁ == g₂) (p₆ : F₁ (str-pf φ₁) g₂ == h₆ ◻ F₁ (str-pf φ₁) f) (p₇ : h₆ == h₇)
            (p₈ : F₁ (str-pf φ₂) (⟦ ξC ⟧ h₆ ◻ F₁ (str-pf φ₁) f) == F₁ (str-pf φ₂) h₆ ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f))
            (p₉ : F₁ (str-pf φ₂) h₇ == k₅) →
            ! (ap (λ m → F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ m) p₁) ∙
            ! (ap (λ m → F₁ (str-pf φ₂) (⟦ ξC ⟧ F₁ (str-pf φ₁) h ◻ m)) (! p₂) ∙ p₃ ∙'
              ! (ap (λ m → ⟦ ξD ⟧ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) h) ◻ F₁ (str-pf φ₂) m) (! p₂))) ∙
            ap (F₁ (str-pf φ₂))
              (! (ap (λ m → F₁ (str-pf φ₁) h ◻ m) p₂) ∙ ! p₄ ∙
              ap (F₁ (str-pf φ₁)) p₅ ∙ p₆ ∙
              ap (λ m → m ◻ F₁ (str-pf φ₁) f) p₇) ∙
            (ap (λ m → F₁ (str-pf φ₂) (⟦ ξC ⟧ m ◻ F₁ (str-pf φ₁) f)) (! p₇) ∙ p₈ ∙'
            ! (ap (λ m → ⟦ ξD ⟧ F₁ (str-pf φ₂) m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) (! p₇))) ∙
            ap (λ m → m ◻ F₁ (str-pf φ₂) (F₁ (str-pf φ₁) f)) p₉
              ==
            ! (ap (λ m → (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) h ◻ m)
                (ap (F₁ (str-pf φ₂)) p₂ ∙ p₁)) ∙
            ! (ap (F₁ (str-pf φ₂)) p₄ ∙ p₃) ∙
            ap (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) p₅ ∙
            (ap (F₁ (str-pf φ₂)) p₆ ∙ p₈) ∙
            ap (λ m → m ◻ (F₁ (str-pf φ₂) ∘ F₁ (str-pf φ₁)) f)
              (ap (F₁ (str-pf φ₂)) p₇ ∙ p₉)
          aux-α idp idp p₃ p₄ idp p₆ idp p₈ idp = aux2-α (F₁ (str-pf φ₂)) p₃ p₄ p₆ p₈
            where
              aux2-α : ∀ {i j} {A : Type i} {B : Type j} (g : A → B) {y₁ y₂ : B} {x₁ x₂ x₃ : A}
                (q₁ : g x₂ == y₁) (q₂ : x₁ == x₂) (q₃ : x₁ == x₃) (q₄ : g x₃ == y₂) →
                ! q₁ ∙ ap g (! q₂ ∙ q₃ ∙ idp) ∙ q₄ ∙ idp == ! (ap g q₂ ∙ q₁) ∙ (ap g q₃ ∙ q₄) ∙ idp
              aux2-α _ idp idp idp idp = idp


-- adjoint equivalence str and example of id map

-- equivalences str between two pseudofunctors (skip pseudotransf definition itself)

-- biequiv strucutre between two bicats
