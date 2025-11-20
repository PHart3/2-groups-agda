{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import Pstransf-ops
open import Pstransf-SIP

-- coherent biadjunction between bicategories

module Biadj where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans
open InvMod

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {L : Psfunctor {{ξB}} {{ξC}}} {R : Psfunctor {{ξC}} {{ξB}}} where

  record Biadj-data (ε : Pstrans (L ∘BC R) idfBC) (η : Pstrans idfBC (R ∘BC L)) :
    Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor biadj-data
    -- the following fields make up coherent versions of triangle identities between η and ε
    field
    
      -- two invertible modifications:
      ζ₁ : 
        pstrans-whisk-r (pstrans-forg η) R pstrans-∙ assoc-psf–> R L R pstrans-∙ pstrans-whisk-l (pstrans-forg ε) R
          ⇔
        unitl-pst–> R pstrans-∙ unitr-pst<– R 
      ζ₂ :  -- eventually, we will derive ζ₂ from ζ₁
        pstrans-whisk-l (pstrans-forg η) L pstrans-∙ assoc-psf<– L R L pstrans-∙ pstrans-whisk-r (pstrans-forg ε) L
          ⇔
        unitr-pst–> L pstrans-∙ unitl-pst<– L
        
      -- two coherence conditions on the modifications:
      ζ-zz₁ : (x : C₀) →
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ m)
          (ap (F₁ (str-pf L)) (ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η (map-pf R x)) (ρ (F₁ (str-pf R) (η₀ ε x))))) ∙
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ F₁ (str-pf L) m) (η₀-∼ ζ₁ x) ∙
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ m) (F-◻ (str-pf L) (id₁ (map-pf R x)) (id₁ (map-pf R x))) ∙
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ ⟦ ξC ⟧ m ◻ m) (F-id₁ (str-pf L) (map-pf R x))
          ==
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ m) (F-◻ (str-pf L) (η₀ η (map-pf R x)) (F₁ (str-pf R) (η₀ ε x))) ∙
        α (η₀ ε x) (F₁ (str-pf L) (F₁ (str-pf R) (η₀ ε x))) (F₁ (str-pf L) (η₀ η (map-pf R x))) ∙
        ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf L) (η₀ η (map-pf R x))) (η₁ ε (η₀ ε x))) ∙
        ! (α (η₀ ε x) (η₀ ε (map-pf L (map-pf R x))) (F₁ (str-pf L) (η₀ η (map-pf R x)))) ∙
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ m)
          (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf L) (η₀ η (map-pf R x))) (ρ (η₀ ε (map-pf L (map-pf R x))))) ∙
        ap (λ m → ⟦ ξC ⟧ η₀ ε x ◻ m) (η₀-∼ ζ₂ (map-pf R x))
      ζ-zz₂ :  (x : B₀) →
        ap (λ m → ⟦ ξB ⟧ F₁ (str-pf R) m ◻ η₀ η x) (η₀-∼ ζ₂ x)
          ==
        ! (ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η x)
          (ap (F₁ (str-pf R)) (ap (λ m → m ◻ F₁ (str-pf L) (η₀ η x)) (ρ (η₀ ε (map-pf L x)))))) ∙
        ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η x) (F-◻ (str-pf R) (F₁ (str-pf L) (η₀ η x)) (η₀ ε (map-pf L x))) ∙
        ! (α (F₁ (str-pf R) (η₀ ε (map-pf L x))) (F₁ (str-pf R) (F₁ (str-pf L) (η₀ η x))) (η₀ η x)) ∙
        ap (λ m → ⟦ ξB ⟧ F₁ (str-pf R) (η₀ ε (map-pf L x)) ◻ m) (η₁ η (η₀ η x)) ∙
        α (F₁ (str-pf R) (η₀ ε (map-pf L x))) (η₀ η (map-pf R (map-pf L x))) (η₀ η x) ∙
        ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η x)
          (ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η (map-pf R (map-pf L x))) (ρ (F₁ (str-pf R) (η₀ ε (map-pf L x))))) ∙
        ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η x) (η₀-∼ ζ₁ (map-pf L x)) ∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ m ◻ η₀ η x) (F-id₁ (str-pf R) (map-pf L x))) ∙
        ! (ap (λ m → ⟦ ξB ⟧ m ◻ η₀ η x) (F-◻ (str-pf R) (id₁ (map-pf L x)) (id₁ (map-pf L x))))
