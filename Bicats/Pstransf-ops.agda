{-# OPTIONS --without-K --rewriting #-}
open import lib.Basics
open import Bicategory
open import Bicat-coher
open import Pstransf

-- non-coherent operations on pseudotransformations

{- Here we omit the proposition-valued coherence conditions of pseudotransformations
   because we only use these operations to formulate the triangle identities of a
   biadjunction (in a different file), which ignore such coherence conditions. -}

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
    ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ ⟦ ξC ⟧ η₀-nc T₂ x ◻ η₀-nc T₁ x
      =⟨ α (F₁ (str-pf R₃) f) (η₀-nc T₂ x) (η₀-nc T₁ x) ⟩
    ⟦ ξC ⟧ ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻  η₀-nc T₂ x ◻ η₀-nc T₁ x
      =⟨ ap (λ m → ⟦ ξC ⟧ m ◻ η₀-nc T₁ x) (η₁-nc T₂ f) ⟩
    ⟦ ξC ⟧ ⟦ ξC ⟧ η₀-nc T₂ y ◻ F₁ (str-pf R₂) f ◻ η₀-nc T₁ x
      =⟨ ! (α (η₀-nc T₂ y) (F₁ (str-pf R₂) f) (η₀-nc T₁ x)) ⟩
    ⟦ ξC ⟧ η₀-nc T₂ y ◻ ⟦ ξC ⟧ F₁ (str-pf R₂) f ◻ η₀-nc T₁ x
      =⟨ ap (λ m → ⟦ ξC ⟧ η₀-nc T₂ y ◻ m) (η₁-nc T₁ f) ⟩
    ⟦ ξC ⟧ η₀-nc T₂ y ◻ ⟦ ξC ⟧ η₀-nc T₁ y ◻ F₁ (str-pf R₁) f
      =⟨ α (η₀-nc T₂ y) (η₀-nc T₁ y) (F₁ (str-pf R₁) f) ⟩
    ⟦ ξC ⟧ (⟦ ξC ⟧ η₀-nc T₂ y ◻ η₀-nc T₁ y) ◻ F₁ (str-pf R₁) f =∎

  -- left whiskering

  -- right whiskering

  -- associativity pseudotransformation (and its inverse)

  -- unit pseudotransformations

