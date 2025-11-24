{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pi
open import lib.wild-cats.WildCats renaming
  (hom to homW; id₁ to id₁W; ρ to ρW; lamb to lambW; α to αW)
open import Bicat-wild
open import Bicategory
open import Bicat-coher
open import AdjEq

module Pstransf where

open BicatStr {{...}}
open Psfunctor-nc
open PsfunctorNcStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}  where

  -- pseudotransformations
  record Pstrans (R S : Psfunctor-nc {{ξB}} {{ξC}}) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor pstrans
    field
      η₀ : (a : B₀) → hom (map-pf R a) (map-pf S a)
      η₁ : {a b : B₀} (f : hom a b) → F₁ (str-pf S) f ◻ η₀ a == ⟦ ξC ⟧ η₀ b ◻ F₁ (str-pf R) f
      coher-unit : {a : B₀} →
        lamb (η₀ a) ∙
        ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a)) ∙
        η₁ (id₁ a) ∙
        ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)
          ==
        ρ (η₀ a)
      coher-assoc : {a b c : B₀} (f : hom a b) (g : hom b c) →
        ! (η₁ (⟦ ξB ⟧ g ◻ f)) ∙
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g))
          ==
        idp
        
    abstract

      coher-unit◃ : {a : B₀} →
        lamb (η₀ a) ◃∙
        ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a)) ◃∙
        η₁ (id₁ a) ◃∙
        ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a) ◃∎
          =ₛ
        ρ (η₀ a) ◃∎
      coher-unit◃ = =ₛ-in coher-unit

      coher-unit◃-rot : {a : B₀} →
        η₁ (id₁ a) ◃∎
          =ₛ
        ap (λ m → m ◻ η₀ a) (F-id₁ (str-pf S) a) ◃∙
        ! (lamb (η₀ a)) ◃∙
        ρ (η₀ a) ◃∙
        ! (ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)) ◃∎
      coher-unit◃-rot {a} =
        η₁ (id₁ a) ◃∎
          =ₛ⟨ post-rotate-in (pre-rotate-in (pre-rotate-in coher-unit◃)) ⟩
        ! (ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a))) ◃∙
        ! (lamb (η₀ a)) ◃∙
        ρ (η₀ a) ◃∙
        ! (ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)) ◃∎
          =ₛ₁⟨ 0 & 1 & !-!-ap (λ m → m ◻ η₀ a) (F-id₁ (str-pf S) a) ⟩
        ap (λ m → m ◻ η₀ a) (F-id₁ (str-pf S) a) ◃∙
        ! (lamb (η₀ a)) ◃∙
        ρ (η₀ a) ◃∙
        ! (ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)) ◃∎ ∎ₛ

      coher-assoc◃ : {a b c : B₀} (f : hom a b) (g : hom b c) →
        ! (η₁ (⟦ ξB ⟧ g ◻ f)) ◃∙
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ◃∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ◃∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ◃∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ◃∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ◃∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g)) ◃∎
            =ₛ
        []
      coher-assoc◃ f g = =ₛ-in (coher-assoc f g)

      coher-assoc◃-rot : {a b c : B₀} (f : hom a b) (g : hom b c) →
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ◃∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ◃∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ◃∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ◃∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ◃∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g)) ◃∎
            =ₛ
        η₁ (⟦ ξB ⟧ g ◻ f) ◃∎
      coher-assoc◃-rot f g = pre-rotate'-out (coher-assoc◃ f g)

  -- pseudonatural equivalence
  infixr 70 _ps-≃_
  _ps-≃_ : Psfunctor-nc {{ξB}} {{ξC}} → Psfunctor-nc {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  F ps-≃ G = Σ (Pstrans F G) (λ φ → (b : B₀) → Adjequiv {{ξC}} (Pstrans.η₀ φ b))

-- induced wild natural transformation
module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  pf-to-wf : Psfunctor-nc {{ξB}} {{ξC}} → Functor-wc (bc-to-wc B) (bc-to-wc C)
  obj (pf-to-wf (psfunctornc map-pf ⦃ σ ⦄)) = map-pf
  arr (pf-to-wf (psfunctornc map-pf ⦃ σ ⦄)) = F₁ σ
  id (pf-to-wf (psfunctornc map-pf ⦃ σ ⦄)) = F-id₁ σ
  comp (pf-to-wf (psfunctornc map-pf ⦃ σ ⦄)) = F-◻ σ

  open Nat-trans
  open Pstrans

  ptr-to-ntr : {φ₁ φ₂ : Psfunctor-nc {{ξB}} {{ξC}}} → Pstrans φ₁ φ₂ → Nat-trans (pf-to-wf φ₁) (pf-to-wf φ₂)
  comp (ptr-to-ntr τ) = η₀ τ
  sq (ptr-to-ntr τ) = η₁ τ

-- non-coherent version of a pseudotransformation
module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}  where

  record Pstrans-nc (R S : Psfunctor-nc {{ξB}} {{ξC}}) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor pstransnc
    field
      η₀ : (a : B₀) → hom (map-pf R a) (map-pf S a)
      η₁ : {a b : B₀} (f : hom a b) → ⟦ ξC ⟧ F₁ (str-pf S) f ◻ η₀ a == ⟦ ξC ⟧ η₀ b ◻ F₁ (str-pf R) f

  open Pstrans
  open Pstrans-nc
  
  --underlying structure of a pseudotransformation
  pstrans-str : {R S : Psfunctor-nc {{ξB}} {{ξC}}} → Pstrans R S → Pstrans-nc R S
  η₀ (pstrans-str ψ) = η₀ ψ
  η₁ (pstrans-str ψ) = η₁ ψ

  -- making Pstrans into a Σ-type
  module _ {R S : Psfunctor-nc {{ξB}} {{ξC}}} where

    Pst-coh-data : Pstrans-nc R S → Type (lmax (lmax i₁ j₁) j₂)
    Pst-coh-data (pstransnc η₀ η₁) =
      ({a : B₀} →
        lamb (η₀ a) ∙
        ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a)) ∙
        η₁ (id₁ a) ∙
        ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)
          ==
        ρ (η₀ a)) ×
      ({a b c : B₀} (f : hom a b) (g : hom b c) →
        ! (η₁ (⟦ ξB ⟧ g ◻ f)) ∙
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g))
          ==
        idp)

    instance
      Pst-coh-data-is-prop : ∀ {ψ} → is-prop (Pst-coh-data ψ)
      Pst-coh-data-is-prop = ×-level ⟨⟩ ⟨⟩

    Pstrans-Σ-≃ : Pstrans R S ≃ Σ (Pstrans-nc R S) Pst-coh-data
    Pstrans-Σ-≃ = equiv
      (λ (pstrans η₀ η₁ cu ca) → (pstransnc η₀ η₁) , (cu , ca))
      (λ ((pstransnc η₀ η₁) , (cu , ca)) → pstrans η₀ η₁ cu ca)
      (λ _ → idp)
      λ _ → idp
