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
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  has-inverse-psf : Psfunctor-nc {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  has-inverse-psf R = Σ (Psfunctor-nc {{ξC}} {{ξB}}) (λ R' → ((R' ∘BC-s R) ps-≃ idpfBC) × (idpfBC ps-≃ (R ∘BC-s R')))

  has-rinv : Psfunctor-nc {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  has-rinv R = Σ (Psfunctor-nc {{ξC}} {{ξB}}) (λ R' → (idpfBC ps-≃ (R ∘BC-s R')))

  is-linv : Psfunctor-nc {{ξB}} {{ξC}} → Psfunctor-nc {{ξC}} {{ξB}} → Type (lmax i₁ j₁)
  is-linv R R' = (R' ∘BC-s R) ps-≃ idpfBC

  psft-rinv-coh-data : {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}}
    {R : Psfunctor {{ξB}} {{ξC}}} → has-rinv (psftor-str R) → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  psft-rinv-coh-data {R} (R' , η) = let R₀ = psftor-str R in
    Σ (is-linv R₀ R') (λ ε →
      uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ R' R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
        ≃-⇔
      unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀) 

  module _ {i₃ j₃} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {R : Psfunctor-nc {{ξB}} {{ξC}}}
    {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}} {{uD : is-univ-bc-inst {{ξD}}}}
    ((R' , li , ri) : has-inverse-psf R) where

    private

      uB-e : is-univ-bc ξB
      uB-e a b = uB {a} {b}

      uC-e : is-univ-bc ξC
      uC-e a b = uC {a} {b}

      uD-e : is-univ-bc ξD
      uD-e a b = uD {a} {b}

    -- induced equivalences on hom types

    bc-ps-≃-hom-dom : (Psfunctor-nc {{ξC}} {{ξD}}) ≃  (Psfunctor-nc {{ξB}} {{ξD}})
    bc-ps-≃-hom-dom = equiv (λ P → P ∘BC-s R) (λ P → P ∘BC-s R')
      (λ P →
        ps-≃-to-== uD-e (assoc-ps-≃ R R' P) ∙
        ap (λ m → P ∘BC-s m) (ps-≃-to-== uB-e li) ∙
        ! (ps-≃-to-== uD-e (unitr-ps-≃ P)))
      λ P → 
        ps-≃-to-== uD-e (assoc-ps-≃ R' R P) ∙
        ! (ap (λ m → P ∘BC-s m) (ps-≃-to-== uC-e ri)) ∙
        ! (ps-≃-to-== uD-e (unitr-ps-≃ P))

    bc-ps-≃-hom-cdom : (Psfunctor-nc {{ξD}} {{ξB}}) ≃  (Psfunctor-nc {{ξD}} {{ξC}})
    bc-ps-≃-hom-cdom = equiv (λ P → R ∘BC-s P) (λ P → R' ∘BC-s P)
      (λ P → 
        ! (ps-≃-to-== uC-e (assoc-ps-≃ P R' R)) ∙
        ! (ap (λ m → m ∘BC-s P) (ps-≃-to-== uC-e ri)) ∙
        ps-≃-to-== uC-e (unitl-ps-≃ P))
      λ P → 
        ! (ps-≃-to-== uB-e (assoc-ps-≃ P R R')) ∙
        ap (λ m → m ∘BC-s P) (ps-≃-to-== uB-e li) ∙
        ps-≃-to-== uB-e (unitl-ps-≃ P)

  module _ {R : Psfunctor-nc {{ξB}} {{ξC}}} {{uB : is-univ-bc-inst {{ξB}}}} {{uC : is-univ-bc-inst {{ξC}}}}
    (hi : has-inverse-psf R) where

    -- the type of right inverses is contractible
    psf-hi-rinv-contr : is-contr (has-rinv R)
    psf-hi-rinv-contr = equiv-preserves-level (Σ-emap-r (λ R' → ps-≃-==-≃ (λ _ _ → uC)))
      {{≃-==-contr (bc-ps-≃-hom-cdom hi)}}
