{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import Bicategory
open import Pstransf
open import AdjEq
open import Univ-bc

-- SIP for pseudofunctors valued in univalent bicategories

module PsFunctor-iso where

open BicatStr
open Psfunctor
open PsfunctorStr {{...}}
open Pstrans

module _ {i₁ i₂ j₁ j₂ : ULevel} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- pseudonatural equivalence
  infixr 70 _iso-pf_
  _iso-pf_ : Psfunctor {{ξB}} {{ξC}} → Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  F iso-pf G = Σ (Pstrans F G) (λ φ → (b : B₀) → Adjequiv (η₀ φ b))

  iso-pf-id : (F : Psfunctor {{ξB}} {{ξC}}) → F iso-pf F
  fst (iso-pf-id F) = {!Pstrans-id F!}
  snd (iso-pf-id F) b = snd AdjEq-id₁
