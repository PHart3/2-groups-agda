{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory

module Biequiv where

open BicatStr {{...}}

module _ {i j} {B₀ : Type i} {{ξ : BicatStr j B₀}} where

  -- adjoint equivalence on a 1-cell
  record Adjequiv {a b : B₀} (f : hom a b) : Type (lmax i j) where
    field
      inv : hom b a
      eta : id₁ a == inv ◻ f
      eps : id₁ b == f ◻ inv
      coher-map : ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps
      coher-inv : lamb inv ∙ ap (λ m → m ◻ inv) eta == ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv

open Psfunctor
open PsfunctorStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}  where

  -- pseudotransformations
  record Pstrans (R S : Psfunctor {{ξB}} {{ξC}}) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      η₀ : (a : B₀) → hom (map-pf R a) (map-pf S a)
      η₁ : {a b : B₀} (f : hom a b) → F₁ (str-pf S) f ◻ η₀ a == η₀ b ◻ F₁ (str-pf R) f
      coher-unit : {a : B₀} →
        lamb (η₀ a) ∙
        ap (λ m → m ◻ η₀ a) (! (F-id₁ (str-pf S) a)) ∙
        η₁ (id₁ a) ∙
        ap (λ m → η₀ a ◻ m) (F-id₁ (str-pf R) a)
          ==
        ρ (η₀ a)
      coher-assoc : {a b c : B₀} (f : hom a b) (g : hom b c) →
        ! (η₁ (g ◻ f)) ∙
        ap (λ m → m ◻ η₀ a) (F-◻ (str-pf S) f g) ∙
        ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (η₀ a)) ∙
        ap (λ m → F₁ (str-pf S) g ◻ m) (η₁ f) ∙
        α (F₁ (str-pf S) g) (η₀ b) (F₁ (str-pf R) f) ∙
        ap (λ m → m ◻ (F₁ (str-pf R) f)) (η₁ g) ∙
        ! (α (η₀ c) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ∙
        ! (ap (λ m → η₀ c ◻ m) (F-◻ (str-pf R) f g))
          ==
        idp
        
module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂}  where

  open Pstrans

  -- biequiv strucutre between two bicats
  
  record BiequivStr-inst {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    field
      Ψ₁ : Psfunctor {{ξB}} {{ξC}} 
      Ψ₂ : Psfunctor {{ξC}} {{ξB}}
      τ₁ : Pstrans (Ψ₁ ∘BC Ψ₂) idfBC
      τ₂ : Pstrans idfBC (Ψ₂ ∘BC Ψ₁)
      lev-eq₁ : (a : C₀) → Adjequiv (η₀ τ₁ a)
      lev-eq₂ : (a : B₀) → Adjequiv (η₀ τ₂ a)

  -- for clarity of final theorem statement
  BiequivStr : (ξB : BicatStr j₁ B₀) (ξC : BicatStr j₂ C₀) → Type (lmax (lmax i₁ j₁) (lmax i₂ j₂))
  BiequivStr ξB ξC = BiequivStr-inst {{ξB}} {{ξC}}
