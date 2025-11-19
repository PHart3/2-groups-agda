{-# OPTIONS --without-K --rewriting #-}
open import lib.Basics
open import Bicategory
open import Bicat-coher
open import Pstransf

-- operations on (non-coherent) pseudotransformations

{- Here we omit the proposition-valued coherence conditions of pseudotransformations
   because we only use these operations, which are completely standard, to formulate
   the triangle identities of a biadjunction (in a different file), which ignore such
   coherence conditions. -}

module Pstransf-ops where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- composition

  infixr 70 _pstrans-∘_
  _pstrans-∘_ : {R₁ R₂ R₃ : Psfunctor {{ξB}} {{ξC}}} → Pstrans-nc R₂ R₃ → Pstrans-nc R₁ R₂ → Pstrans-nc R₁ R₃
  η₀-nc (T₂ pstrans-∘ T₁) a = η₀-nc T₂ a ◻ η₀-nc T₁ a
  η₁-nc (_pstrans-∘_ {R₁} {R₂} {R₃} T₂ T₁) {x} {y} f = 
    -- ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ ⟦ ξC ⟧ η₀-nc T₂ x ◻ η₀-nc T₁ x
    α (F₁ (str-pf R₃) f) (η₀-nc T₂ x) (η₀-nc T₁ x) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ F₁ (str-pf R₃) f ◻  η₀-nc T₂ x) ◻ η₀-nc T₁ x
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀-nc T₁ x) (η₁-nc T₂ f) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀-nc T₂ y ◻ F₁ (str-pf R₂) f) ◻ η₀-nc T₁ x
    ! (α (η₀-nc T₂ y) (F₁ (str-pf R₂) f) (η₀-nc T₁ x)) ∙
    -- ⟦ ξC ⟧ η₀-nc T₂ y ◻ ⟦ ξC ⟧ F₁ (str-pf R₂) f ◻ η₀-nc T₁ x
    ap (λ m → ⟦ ξC ⟧ η₀-nc T₂ y ◻ m) (η₁-nc T₁ f) ∙
    -- ⟦ ξC ⟧ η₀-nc T₂ y ◻ ⟦ ξC ⟧ η₀-nc T₁ y ◻ F₁ (str-pf R₁) f
    α (η₀-nc T₂ y) (η₀-nc T₁ y) (F₁ (str-pf R₁) f)
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀-nc T₂ y ◻ η₀-nc T₁ y) ◻ F₁ (str-pf R₁) f

  -- whiskering
  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ R₂ : Psfunctor {{ξB}} {{ξC}}} where

    pstrans-whisk-r : (τ : Pstrans-nc R₁ R₂) (G : Psfunctor {{ξC}} {{ξD}}) → Pstrans-nc (G ∘BC R₁) (G ∘BC R₂)
    η₀-nc (pstrans-whisk-r τ G) x = F₁ (str-pf G) (η₀-nc τ x)
    η₁-nc (pstrans-whisk-r τ G) {x} {y} f = 
      -- ⟦ ξC ⟧ F₁ (str-pf G) (F₁ (str-pf R₂) f) ◻ F₁ (str-pf G) (η₀-nc τ x)
      ! (F-◻ (str-pf G) (η₀-nc τ x) (F₁ (str-pf R₂) f)) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ F₁ (str-pf R₂) f ◻ η₀-nc τ x)
      ap (F₁ (str-pf G)) (η₁-nc τ f) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ η₀-nc τ y ◻ F₁ (str-pf R₁) f)
      F-◻ (str-pf G) (F₁ (str-pf R₁) f) (η₀-nc τ y)
      -- ⟦ ξC ⟧ F₁ (str-pf G) (η₀-nc τ y) ◻ F₁ (str-pf G) (F₁ (str-pf R₁) f)

    pstrans-whisk-l : (τ : Pstrans-nc R₁ R₂) (G : Psfunctor {{ξD}} {{ξB}}) → Pstrans-nc (R₁ ∘BC G) (R₂ ∘BC G)
    η₀-nc(pstrans-whisk-l τ G) x = η₀-nc τ (map-pf G x)
    η₁-nc (pstrans-whisk-l τ G) f = η₁-nc τ (F₁ (str-pf G) f)

  -- associativity pseudotransformation (and its inverse)
  module _ {i₃ i₄ j₃ j₄} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {E₀ : Type i₄} {{ξE : BicatStr j₄ E₀}}
    {R₁ : Psfunctor {{ξB}} {{ξC}}} {R₂ : Psfunctor {{ξC}} {{ξD}}} {R₃ : Psfunctor {{ξD}} {{ξE}}} where

    assoc-psf–> : Pstrans-nc (R₃ ∘BC (R₂ ∘BC R₁)) ((R₃ ∘BC R₂) ∘BC R₁)
    η₀-nc assoc-psf–> a = id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))
    η₁-nc assoc-psf–> {a} {b} f = {!!}

    assoc-psf<– : Pstrans-nc ((R₃ ∘BC R₂) ∘BC R₁) (R₃ ∘BC (R₂ ∘BC R₁))
    η₀-nc assoc-psf<– a = id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))
    η₁-nc assoc-psf<– {a} {b} f = {!!}

  -- unit pseudotransformations
  module _ {R : Psfunctor {{ξB}} {{ξC}}} where
