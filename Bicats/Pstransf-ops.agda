{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import Psftor-SIP
open import Pstransf-id
open import Univ-bc

-- operations on pseudotransformations

module Pstransf-ops where

open BicatStr {{...}}
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans-nc

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- composition
  
  infixr 10 _pstrans-∙_
  _pstrans-∙_ : {R₁ R₂ R₃ : Psfunctor-nc {{ξB}} {{ξC}}} → Pstrans-nc R₁ R₂ → Pstrans-nc R₂ R₃ → Pstrans-nc R₁ R₃
  η₀ (T₁ pstrans-∙ T₂) a = ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a
  η₁ (_pstrans-∙_ {R₁} {R₂} {R₃} T₁ T₂) {x} {y} f = 
    -- ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ ⟦ ξC ⟧ η₀ T₂ x ◻ η₀ T₁ x
    α (F₁ (str-pf R₃) f) (η₀ T₂ x) (η₀ T₁ x) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ F₁ (str-pf R₃) f ◻  η₀ T₂ x) ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ x) (η₁ T₂ f) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ F₁ (str-pf R₂) f) ◻ η₀ T₁ x
    ! (α (η₀ T₂ y) (F₁ (str-pf R₂) f) (η₀ T₁ x)) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ F₁ (str-pf R₂) f ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ y ◻ m) (η₁ T₁ f) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ η₀ T₁ y ◻ F₁ (str-pf R₁) f
    α (η₀ T₂ y) (η₀ T₁ y) (F₁ (str-pf R₁) f)
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ η₀ T₁ y) ◻ F₁ (str-pf R₁) f

  infixr 10 _ps-≃-∙_
  _ps-≃-∙_ : is-univ-bc ξC → {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
    R₁ ps-≃ R₂ → {R₃ : Psfunctor-nc {{ξB}} {{ξC}}} → R₂ ps-≃ R₃ → R₁ ps-≃ R₃
  _ps-≃-∙_ uC {R₁} = psftor-ind uC (λ R₂ pe → ∀ {R₃} → R₂ ps-≃ R₃ → R₁ ps-≃ R₃) λ pe → pe

  -- whiskering
  
  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} where

    pstrans-whisk-l : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      Pstrans-nc R₁ R₂ → (G : Psfunctor-nc {{ξC}} {{ξD}}) → Pstrans-nc (G ∘BC-s R₁) (G ∘BC-s R₂)
    η₀ (pstrans-whisk-l τ G) x = F₁ (str-pf G) (η₀ τ x)
    η₁ (pstrans-whisk-l {R₂} τ G) {x} {y} f = 
      -- ⟦ ξC ⟧ F₁ (str-pf G) (F₁ (str-pf R₂) f) ◻ F₁ (str-pf G) (η₀ τ x)
      ! (F-◻ (str-pf G) (η₀ τ x) (F₁ (str-pf R₂) f)) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ F₁ (str-pf R₂) f ◻ η₀ τ x)
      ap (F₁ (str-pf G)) (η₁ τ f) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ η₀ τ y ◻ F₁ (str-pf R₁) f)
      F-◻ (str-pf G) (F₁ (str-pf R₁) f) (η₀ τ y)
      -- ⟦ ξC ⟧ F₁ (str-pf G) (η₀ τ y) ◻ F₁ (str-pf G) (F₁ (str-pf R₁) f)

    pstrans-whisk-r : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      Pstrans-nc R₁ R₂ → (G : Psfunctor-nc {{ξD}} {{ξB}}) → Pstrans-nc (R₁ ∘BC-s G) (R₂ ∘BC-s G)
    η₀(pstrans-whisk-r τ G) x = η₀ τ (map-pf G x)
    η₁ (pstrans-whisk-r τ G) f = η₁ τ (F₁ (str-pf G) f)

    ps-≃-whisk-l : is-univ-bc ξC → {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      R₁ ps-≃ R₂ → (G : Psfunctor-nc {{ξC}} {{ξD}}) → (G ∘BC-s R₁) ps-≃ (G ∘BC-s R₂)
    ps-≃-whisk-l uC = psftor-ind uC (λ R₂ pe → ∀ G → (G ∘BC-s R₁) ps-≃ (G ∘BC-s R₂)) λ _ → ps-≃-id

    ps-≃-whisk-r : is-univ-bc ξC → {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} →
      R₁ ps-≃ R₂ → (G : Psfunctor-nc {{ξD}} {{ξB}}) → (R₁ ∘BC-s G) ps-≃ (R₂ ∘BC-s G)
    ps-≃-whisk-r uC = psftor-ind uC (λ R₂ pe → ∀ G → (R₁ ∘BC-s G) ps-≃ (R₂ ∘BC-s G)) λ _ → ps-≃-id
