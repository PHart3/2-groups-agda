{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import Bicategory
open import Pstransf
open import Pstransf-SIP
open import Psftor-SIP
open import Psftor-laws
open import Pstransf-ops
open import Univ-bc

-- basic properties of pseudofunctors with a two-sided inverse

module Psftor-inverse where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  has-inverse-psf : Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  has-inverse-psf R = Σ (Psfunctor {{ξC}} {{ξB}}) (λ R' → (psftor-str (R' ∘BC R) ps-≃ idpfBC) × (idpfBC ps-≃ psftor-str (R ∘BC R')))

  has-rinv-psf : Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  has-rinv-psf R = Σ (Psfunctor {{ξC}} {{ξB}}) (λ R' → (idpfBC ps-≃ psftor-str (R ∘BC R')))

  is-linv-psf : Psfunctor {{ξB}} {{ξC}} → Psfunctor {{ξC}} {{ξB}} → Type (lmax i₁ j₁)
  is-linv-psf R R' = psftor-str (R' ∘BC R) ps-≃ idpfBC

  psft-rinv-coh-data : {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}}
    {R : Psfunctor {{ξB}} {{ξC}}} → has-rinv-psf R → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  psft-rinv-coh-data {R} (R' , η) = let R₀ = psftor-str R in
    Σ (is-linv-psf R R') (λ ε →
      uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ (psftor-str R') R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
        ≃-⇔
      unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀) 

  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R : Psfunctor {{ξB}} {{ξC}}}
    {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}} {{uD : is-univ-bc-inst {{ξD}}}}
    ((R' , li , ri) : has-inverse-psf R) where

    private

      uB-e : is-univ-bc ξB
      uB-e a b = uB {a} {b}

      uC-e : is-univ-bc ξC
      uC-e a b = uC {a} {b}

      uD-e : is-univ-bc ξD
      uD-e a b = uD {a} {b}

      R₀ : Psfunctor-nc {{ξB}} {{ξC}}
      R₀ = psftor-str R

      R₀' : Psfunctor-nc {{ξC}} {{ξB}}
      R₀' = psftor-str R'

    -- induced equivalences on hom types

    bc-ps-≃-hom-dom : (Psfunctor {{ξC}} {{ξD}}) ≃ (Psfunctor {{ξB}} {{ξD}})
    bc-ps-≃-hom-dom = equiv (λ P → P ∘BC R) (λ P → P ∘BC R')
      (λ P →
        psf-≃-to-== uD-e (assoc-ps-≃ R₀ R₀' (psftor-str P)) ∙
        ap (λ m → P ∘BC m) (psf-≃-to-== uB-e {R' ∘BC R} {idfBC} li) ∙
        ! (psf-≃-to-== uD-e (unitr-ps-≃ (psftor-str P))))
      λ P → 
        psf-≃-to-== uD-e (assoc-ps-≃ R₀' R₀ (psftor-str P)) ∙
        ! (ap (λ m → P ∘BC m) (psf-≃-to-== uC-e {idfBC} {R ∘BC R'} ri)) ∙
        ! (psf-≃-to-== uD-e (unitr-ps-≃ (psftor-str P)))

    bc-ps-≃-hom-cdom : (Psfunctor {{ξD}} {{ξB}}) ≃ (Psfunctor {{ξD}} {{ξC}})
    bc-ps-≃-hom-cdom = equiv (λ P → R ∘BC P) (λ P → R' ∘BC P)
      (λ P → 
        ! (psf-≃-to-== uC-e (assoc-ps-≃  (psftor-str P) R₀' R₀)) ∙
        ! (ap (λ m → m ∘BC P) (psf-≃-to-== uC-e {idfBC} {R ∘BC R'} ri)) ∙
        psf-≃-to-== uC-e (unitl-ps-≃ (psftor-str P)))
      λ P → 
        ! (psf-≃-to-== uB-e (assoc-ps-≃ (psftor-str P) R₀ R₀')) ∙
        ap (λ m → m ∘BC P) (psf-≃-to-== uB-e {R' ∘BC R} {idfBC} li) ∙
        psf-≃-to-== uB-e (unitl-ps-≃ (psftor-str P))

    nc-ps-≃-hom-cdom : (Psfunctor-nc {{ξD}} {{ξB}}) ≃  (Psfunctor-nc {{ξD}} {{ξC}})
    nc-ps-≃-hom-cdom = equiv (λ P → R₀ ∘BC-s P) (λ P → R₀' ∘BC-s P)
      (λ P → 
        ! (ps-≃-to-== uC-e (assoc-ps-≃ P R₀' R₀)) ∙
        ! (ap (λ m → m ∘BC-s P) (ps-≃-to-== uC-e ri)) ∙
        ps-≃-to-== uC-e (unitl-ps-≃ P))
      λ P → 
        ! (ps-≃-to-== uB-e (assoc-ps-≃ P R₀ R₀')) ∙
        ap (λ m → m ∘BC-s P) (ps-≃-to-== uB-e li) ∙
        ps-≃-to-== uB-e (unitl-ps-≃ P)

  -- the type of right inverses is contractible
  module _ {R : Psfunctor {{ξB}} {{ξC}}} {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}} (hi : has-inverse-psf R) where

    psf-has-rinv-unique : {R₁ R₂ : Psfunctor {{ξC}} {{ξB}}} →
      idpfBC ps-≃ psftor-str (R ∘BC R₁) → idpfBC ps-≃ psftor-str (R ∘BC R₂) → R₁ == R₂
    psf-has-rinv-unique ri1 ri2 = equiv-is-inj (snd (bc-ps-≃-hom-cdom {R = R} hi)) _ _
      (! (psf-≃-to-== (λ _ _ → uC) ri1) ∙ (psf-≃-to-== (λ _ _ → uC) {idfBC} ri2)) 

    abstract
      psf-hi-rinv-contr : is-contr (has-rinv-psf R)
      psf-hi-rinv-contr = equiv-preserves-level (Σ-emap-r (λ R' → psf-≃-==-≃  (λ _ _ → uC) {idfBC} {R ∘BC R'}))
        {{≃-==-contr (bc-ps-≃-hom-cdom hi)}}
