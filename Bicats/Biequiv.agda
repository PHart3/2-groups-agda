{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEqv
open import Biadj
open import Univ-bc
open import Psftor-inverse

module Biequiv where

open BicatStr {{...}}

open import Pstransf public
open Pstrans

module _ {i₁ i₂ j₁ j₂} {C₀ : Type i₂} {B₀ : Type i₁}  where

  -- biequivalence structure between two bicats
  
  record BiequivStr-inst {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}} : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bequiv
    field
      Ψ-L : Psfunctor {{ξB}} {{ξC}}
      Ψ-R : Psfunctor {{ξC}} {{ξB}}
      ε : (psftor-str (Ψ-L ∘BC Ψ-R)) psf-≃ idpfBC
      η : idpfBC psf-≃ (psftor-str (Ψ-R ∘BC Ψ-L))

    τ₁ : Pstrans (psftor-str (Ψ-L ∘BC Ψ-R)) idpfBC
    τ₁ = fst ε

    τ₂ : Pstrans idpfBC (psftor-str (Ψ-R ∘BC Ψ-L))
    τ₂ = fst η

    lev-eq₁ : (a : C₀) → Adjequiv {{ξC}} (η₀ τ₁ a)
    lev-eq₁ a = snd ε a

    lev-eq₂ : (a : B₀) → Adjequiv {{ξB}} (η₀ τ₂ a)
    lev-eq₂ a = snd η a

  -- for clarity of final theorem statement
  BiequivStr : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → Type (lmax (lmax i₁ j₁) (lmax i₂ j₂))
  BiequivStr ξC ξB = BiequivStr-inst {{ξC}} {{ξB}}

  -- biadjoint biequivalences
  infixr 70 _biadj-bieqv_
  _biadj-bieqv_ : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  ξC biadj-bieqv ξB = Σ (BiequivStr ξC ξB) (λ be →
    Biequiv-coh {{ξC}} {{ξB}} {R = Ψ-R {{ξC}} {{ξB}} be} {L = Ψ-L {{ξC}} {{ξB}} be}
    (ε {{ξC}} {{ξB}} be) (η {{ξC}} {{ξB}} be)) where open BiequivStr-inst

  -- the property of being a biadjoint biequivalence (formulated for univalent bicategories)
  is-biadj-bieqv : {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}}
    {{uC : is-univ-bc-inst {{ξC}}}} {{uB : is-univ-bc-inst {{ξB}}}}
    → Psfunctor {{ξC}} {{ξB}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-biadj-bieqv R = Σ (has-rinv-psf R) (psft-rinv-coh-data {R = R})
