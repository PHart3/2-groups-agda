{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Paths
open import Bicategory
open import Pstransf
open import Pstransf-ops
open import Pstransf-SIP
open import Psftor-SIP
open import Psftor-laws
open import Psnat-equiv-conv
open import Psftor-inverse
open import Univ-bc

{- coherence data for a biequivalence between univalent bicategories,
   namely one of the triangulators of a biadjunction -}

module Biadj where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans
open InvMod

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂}  {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}}
  {L : Psfunctor {{ξB}} {{ξC}}} {R : Psfunctor {{ξC}} {{ξB}}} 
  {{uC : is-univ-bc-inst {{ξC}}}} {{uB : is-univ-bc-inst {{ξB}}}} where

  private
    L₀ = psftor-str L
    R₀ = psftor-str R

  record Biequiv-coh (ε : (psftor-str (L ∘BC R)) ps-≃ idpfBC) (η : idpfBC ps-≃ (psftor-str (R ∘BC L))) :
    Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bieqvcoh
    field
      -- the zig-zag triangulator
      ζζ :  
        uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
          ≃-⇔
        unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀

  {- For a biequivalence between univalent bicategoires, as soon as we have ζζ, we have
     a contractible choice of the remaining data of a biadjunction, i.e., the other zig-zag
     identity along with the two swallowtail identities. -}

  
  module _ (η : idpfBC ps-≃ (psftor-str (R ∘BC L)))  where

    private

      uB-e : is-univ-bc ξB
      uB-e a b = uB {a} {b}

      uC-e : is-univ-bc ξC
      uC-e a b = uC {a} {b}

      η-i : idpfBC == psftor-str (R ∘BC L)
      η-i = ps-≃-to-== uB-e η

    biadj-zz-== : (ε : (psftor-str (L ∘BC R)) ps-≃ idpfBC) →
      (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
        ≃-⇔
      unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀)
        ≃
      (ap (λ m → m ∘BC-s R₀) η-i ∙ ps-≃-to-== uB-e (assoc-ps-≃ R₀ L₀ R₀) ∙ ap (λ m → R₀ ∘BC-s m) (ps-≃-to-== uC-e ε)
        ==
      ps-≃-to-== uB-e (unitl-ps-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-ps-≃ R₀))
    biadj-zz-== ε =
      let
        ε-i : psftor-str (L ∘BC R) == idpfBC
        ε-i = ps-≃-to-== uC-e ε
      in
      (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
        ≃-⇔
      unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀)
        ≃⟨ ps-≃-InvMod-==-≃ ⁻¹ ⟩
      (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
        ==
      (unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀)
        ≃⟨ ap-equiv ((ps-≃-==-≃ uB-e)⁻¹) _ _ ⟩
      (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
        ==
      ps-≃-to-== uB-e (unitl-ps-≃ R₀ uvpsnat-≃-∙ unitr-ps-≃ R₀))
        ≃⟨ post∙-equiv (psnat-≃-∙-pres uB-e (unitl-ps-≃ R₀) (unitr-ps-≃ R₀)) ⟩
      (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-ps-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
        ==
      ps-≃-to-== uB-e (unitl-ps-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-ps-≃ R₀))
        ≃⟨ pre∙-equiv (! (psnat-≃-∙-pres-tri uB-e
             (uvpsnat-≃-whisk-r η R₀) (assoc-ps-≃ R₀ L₀ R₀) (uvpsnat-≃-whisk-l ε R))) ⟩
      (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀) ∙
      ps-≃-to-== uB-e (assoc-ps-≃ R₀ L₀ R₀) ∙
      ps-≃-to-== uB-e (uvpsnat-≃-whisk-l ε R)
        ==
      ps-≃-to-== uB-e (unitl-ps-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-ps-≃ R₀))
        ≃⟨ pre∙-equiv (! (ap2 (λ p₁ p₂ → p₁ ∙ ps-≃-to-== uB-e (assoc-ps-≃ R₀ L₀ R₀) ∙ p₂)
             (psnat-≃-whisk-r-pres uB-e η R₀)
             (psnat-≃-whisk-l-pres uC-e uB-e ε R))) ⟩
      ap (λ m → m ∘BC-s R₀) η-i ∙ ps-≃-to-== uB-e (assoc-ps-≃ R₀ L₀ R₀) ∙ ap (λ m → R₀ ∘BC-s m) ε-i
        ==
      ps-≃-to-== uB-e (unitl-ps-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-ps-≃ R₀) ≃∎

    abstract
      bae-rinv-cd-contr : (psftor-str (L ∘BC R)) ps-≃ idpfBC → is-contr (psft-rinv-coh-data (L₀ , η))
      bae-rinv-cd-contr ε = equiv-preserves-level ((Σ-emap-r (λ eps → biadj-zz-== eps)) ⁻¹)
        {{∙2-≃-∘-contr ((ps-≃-==-≃ uC-e)⁻¹) (bc-ps-≃-hom-cdom (L₀ , ε , η))
          (ap (λ m → m ∘BC-s R₀) η-i) (ps-≃-to-==  uB-e (assoc-ps-≃ R₀ L₀ R₀))}}
