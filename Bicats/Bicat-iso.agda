{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import Bicategory

-- isomorphism of (2,1)-categories

module Bicat-iso where

open BicatStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {{ξB : BicatStr j₁ B₀}} {C₀ : Type i₂} {{ξC : BicatStr j₂ C₀}} where

  open Psfunctor
  open PsfunctorStr {{...}}

  is-iso-bc : Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-iso-bc φ = is-equiv (map-pf φ) × ((a b : B₀) → is-equiv (F₁ {a = a} {b}))
  
