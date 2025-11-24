{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import Pstransf-id
open import Pstransf-SIP

-- operations on (non-coherent) pseudotransformations

{- Here we omit the proposition-valued coherence conditions of pseudotransformations
   because we only use these operations, which are completely standard, to formulate
   the triangle identities of a biadjunction (in a different file), which ignore such
   coherence conditions. -}

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

  -- whiskering
  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} where

    pstrans-whisk-l : (τ : Pstrans-nc R₁ R₂) (G : Psfunctor-nc {{ξC}} {{ξD}}) → Pstrans-nc (G ∘BC-s R₁) (G ∘BC-s R₂)
    η₀ (pstrans-whisk-l τ G) x = F₁ (str-pf G) (η₀ τ x)
    η₁ (pstrans-whisk-l τ G) {x} {y} f = 
      -- ⟦ ξC ⟧ F₁ (str-pf G) (F₁ (str-pf R₂) f) ◻ F₁ (str-pf G) (η₀ τ x)
      ! (F-◻ (str-pf G) (η₀ τ x) (F₁ (str-pf R₂) f)) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ F₁ (str-pf R₂) f ◻ η₀ τ x)
      ap (F₁ (str-pf G)) (η₁ τ f) ∙
      -- F₁ (str-pf G) (⟦ ξB ⟧ η₀ τ y ◻ F₁ (str-pf R₁) f)
      F-◻ (str-pf G) (F₁ (str-pf R₁) f) (η₀ τ y)
      -- ⟦ ξC ⟧ F₁ (str-pf G) (η₀ τ y) ◻ F₁ (str-pf G) (F₁ (str-pf R₁) f)

    pstrans-whisk-r : (τ : Pstrans-nc R₁ R₂) (G : Psfunctor-nc {{ξD}} {{ξB}}) → Pstrans-nc (R₁ ∘BC-s G) (R₂ ∘BC-s G)
    η₀(pstrans-whisk-r τ G) x = η₀ τ (map-pf G x)
    η₁ (pstrans-whisk-r τ G) f = η₁ τ (F₁ (str-pf G) f)

  -- associativity pseudotransformation (and its inverse)
  module _ {i₃ i₄ j₃ j₄} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {E₀ : Type i₄} {{ξE : BicatStr j₄ E₀}}
    (R₁ : Psfunctor-nc {{ξB}} {{ξC}}) (R₂ : Psfunctor-nc {{ξC}} {{ξD}}) (R₃ : Psfunctor-nc {{ξD}} {{ξE}}) where

    assoc-psf–> : Pstrans-nc ((R₃ ∘BC-s R₂) ∘BC-s R₁) (R₃ ∘BC-s (R₂ ∘BC-s R₁))
    η₀ assoc-psf–> a = id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))
    η₁ assoc-psf–> f = 
      ! (ρ (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))) ∙
      lamb (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))

    assoc-psf<– : Pstrans-nc (R₃ ∘BC-s (R₂ ∘BC-s R₁)) ((R₃ ∘BC-s R₂) ∘BC-s R₁)
    η₀ assoc-psf<– a = id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))
    η₁ assoc-psf<– f =
      ! (ρ (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))) ∙
      lamb (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))

  -- unit pseudotransformations (and their inverses)
  module _ (R : Psfunctor-nc {{ξB}} {{ξC}}) where

    unitl-pst–> : Pstrans-nc (idpfBC ∘BC-s R) R
    η₀ unitl-pst–> a = id₁ (map-pf R a)
    η₁ unitl-pst–> f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)

    unitl-pst<– : Pstrans-nc R (idpfBC ∘BC-s R)
    η₀ unitl-pst<– a = id₁ (map-pf R a)
    η₁ unitl-pst<– f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)

    unitr-pst–> : Pstrans-nc (R ∘BC-s idpfBC) R
    η₀ unitr-pst–> a = id₁ (map-pf R a)
    η₁ unitr-pst–> f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)

    unitr-pst<– : Pstrans-nc R (R ∘BC-s idpfBC)
    η₀ unitr-pst<– a = id₁ (map-pf R a)
    η₁ unitr-pst<– f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)
