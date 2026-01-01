{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import AdjEqv
open import Psftor-SIP
open import Pstransf-id
open import Pstransf-SIP
open import Univ-bc
open import Pstransf-ops

module Psnat-equiv-conv where

open BicatStr {{...}}
open Psfunctor
open PsftorStr
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans-nc

-- some groupoid preservation properties of ps-≃-to-==

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} (uC : is-univ-bc ξC) where

  abstract

    psnat-≃-∙-pres : {R₁ R₃ R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T₁ : R₁ psf-≃ R₂) (T₂ : R₂ psf-≃ R₃) →
      ps-≃-to-== uC (psnat-≃-∙ uC T₁ T₂) == ps-≃-to-== uC T₁ ∙ ps-≃-to-== uC T₂ 
    psnat-≃-∙-pres {R₁} {R₃} = psftor-ind uC
      (λ R₂ T₁ → (T₂ : R₂ psf-≃ R₃) → ps-≃-to-== uC (psnat-≃-∙ uC T₁ T₂) == ps-≃-to-== uC T₁ ∙ ps-≃-to-== uC T₂)
      λ T₂ → ap (ps-≃-to-== uC) (psnat-≃-∙-β uC) ∙ ap (λ t → t ∙ ps-≃-to-== uC T₂) (! (ps-≃-to-==-β uC))

    psnat-≃-∙-pres-tri : {R₁ R₂ R₃ R₄ : Psfunctor-nc {{ξB}} {{ξC}}} (T₁ : R₁ psf-≃ R₂) (T₂ : R₂ psf-≃ R₃) (T₃ : R₃ psf-≃ R₄)
      → ps-≃-to-== uC (psnat-≃-∙ uC T₁ (psnat-≃-∙ uC T₂ T₃)) == ps-≃-to-== uC T₁ ∙ ps-≃-to-== uC T₂ ∙ ps-≃-to-== uC T₃  
    psnat-≃-∙-pres-tri T₁ T₂ T₃ = psnat-≃-∙-pres T₁ (psnat-≃-∙ uC T₂ T₃) ∙ ap (λ t → ps-≃-to-== uC T₁ ∙ t) (psnat-≃-∙-pres T₂ T₃)

  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R₁ : Psfunctor-nc {{ξB}} {{ξC}}} where

    abstract

      psnat-≃-whisk-l-pres : (uD : is-univ-bc ξD)
        {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T : R₁ psf-≃ R₂) (G : Psfunctor {{ξC}} {{ξD}}) → 
        ps-≃-to-== uD (psnat-≃-whisk-l uC T G) == ap (λ m → (psftor-str G) ∘BC-s m) (ps-≃-to-== uC T)
      psnat-≃-whisk-l-pres uD = psftor-ind uC
        (λ R₂ T → ∀ G → ps-≃-to-== uD (psnat-≃-whisk-l uC T G) == ap (λ m → (psftor-str G) ∘BC-s m) (ps-≃-to-== uC T))
        λ G →
          ap (ps-≃-to-== uD) (psnat-≃-whisk-l-β uC {T = ps-≃-id} G) ∙
          ps-≃-to-==-β uD ∙
          ! (ap (ap (λ m → (psftor-str G) ∘BC-s m)) (ps-≃-to-==-β uC))

      psnat-≃-whisk-r-pres : {R₂ : Psfunctor-nc {{ξB}} {{ξC}}} (T : R₁ psf-≃ R₂) (G : Psfunctor-nc {{ξD}} {{ξB}}) → 
        ps-≃-to-== uC (psnat-≃-whisk-r uC T G) == ap (λ m → m ∘BC-s G) (ps-≃-to-== uC T)
      psnat-≃-whisk-r-pres = psftor-ind uC
        (λ R₂ T → ∀ G → ps-≃-to-== uC (psnat-≃-whisk-r uC T G) == ap (λ m → m ∘BC-s G) (ps-≃-to-== uC T))
        λ G →
          ap (ps-≃-to-== uC) (psnat-≃-whisk-r-β uC {T = ps-≃-id} G) ∙
          ps-≃-to-==-β uC ∙
          ! (ap (ap (λ m → m ∘BC-s G)) (ps-≃-to-==-β uC))
