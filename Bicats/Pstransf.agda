{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats renaming
  (hom to homW; id₁ to id₁W; ρ to ρW; lamb to lambW; α to αW)
open import Bicat-wild
open import Bicategory
open import Bicat-coher
open import AdjEq

module Pstransf where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}  where

  -- pseudotransformations
  record Pstrans (R S : Psfunctor {{ξB}} {{ξC}}) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
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

  -- pseudonatural equivalence
  infixr 70 _ps-≃_
  _ps-≃_ : Psfunctor {{ξB}} {{ξC}} → Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  F ps-≃ G = Σ (Pstrans F G) (λ φ → (b : B₀) → Adjequiv {{ξC}} (Pstrans.η₀ φ b))

-- induced wild functor
module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  pf-to-wf : Psfunctor {{ξB}} {{ξC}} → Functor-wc (bc-to-wc B) (bc-to-wc C)
  obj (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = map-pf
  arr (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F₁ σ
  id (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F-id₁ σ
  comp (pf-to-wf (psfunctor map-pf ⦃ σ ⦄)) = F-◻ σ

  open Nat-trans
  open Pstrans

  ptr-to-ntr : {φ₁ φ₂ : Psfunctor {{ξB}} {{ξC}}} → Pstrans φ₁ φ₂ → Nat-trans (pf-to-wf φ₁) (pf-to-wf φ₂)
  comp (ptr-to-ntr τ) = η₀ τ
  sq (ptr-to-ntr τ) = η₁ τ
