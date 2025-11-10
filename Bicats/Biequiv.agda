{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import Bicat-wild

module Biequiv where

open BicatStr {{...}}

open import Pstransf public
        
module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂}  where

  open Pstrans

  -- biequiv structure between two bicats
  
  record BiequivStr-inst {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bequiv
    field
      Ψ₁ : Psfunctor {{ξB}} {{ξC}} 
      Ψ₂ : Psfunctor {{ξC}} {{ξB}}
      ε₁ : (Ψ₁ ∘BC Ψ₂) ps-≃ idfBC
      ε₂ : idfBC ps-≃ (Ψ₂ ∘BC Ψ₁)

    τ₁ : Pstrans (Ψ₁ ∘BC Ψ₂) idfBC
    τ₁ = fst ε₁

    τ₂ : Pstrans idfBC (Ψ₂ ∘BC Ψ₁)
    τ₂ = fst ε₂

    lev-eq₁ : (a : C₀) → Adjequiv {{ξC}} (η₀ τ₁ a)
    lev-eq₁ a = snd ε₁ a

    lev-eq₂ : (a : B₀) → Adjequiv {{ξB}} (η₀ τ₂ a)
    lev-eq₂ a = snd ε₂ a

  -- for clarity of final theorem statement
  BiequivStr : (ξB : BicatStr j₁ B₀) (ξC : BicatStr j₂ C₀) → Type (lmax (lmax i₁ j₁) (lmax i₂ j₂))
  BiequivStr ξB ξC = BiequivStr-inst {{ξB}} {{ξC}}

module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  open BiequivStr-inst
  open Equiv-wc

  -- every biequivalence induces an equivalence of wild categories
  beqv-to-niso : BiequivStr ξB ξC → Equiv-wc (bc-to-wc B) (bc-to-wc C)
  ftor₁ (beqv-to-niso be) = pf-to-wf (Ψ₁ be)
  ftor₂ (beqv-to-niso be) = pf-to-wf (Ψ₂ be)
  fst (iso₁ (beqv-to-niso be)) = ptr-to-ntr (τ₁ be)
  snd (iso₁ (beqv-to-niso be)) x = aeqv-to-weqv (lev-eq₁ be x)
  fst (iso₂ (beqv-to-niso be)) = ptr-to-ntr (τ₂ be)
  snd (iso₂ (beqv-to-niso be)) x = aeqv-to-weqv (lev-eq₂ be x)

  open Psfunctor
  open PsfunctorStr

  -- Every biequivalence is fully faithful.
  abstract
    beqv-is-ff : (be : BiequivStr ξB ξC) → {x y : B₀} → is-equiv (F₁ (str-pf (Ψ₁ be)) {x} {y})
    beqv-is-ff be = Equiv-wc-ff (beqv-to-niso be)
