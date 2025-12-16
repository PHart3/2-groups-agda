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
  {R : Psfunctor {{ξC}} {{ξB}}} {L : Psfunctor {{ξB}} {{ξC}}} where

  private
    L₀ = psftor-str L
    R₀ = psftor-str R

  record Biequiv-coh (ε : (psftor-str (L ∘BC R)) psf-≃ idpfBC) (η : idpfBC psf-≃ (psftor-str (R ∘BC L))) :
      Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
      constructor bieqvcoh
      field
        -- the zig-zag triangulator
        ζζ :  
          pstrans-whisk-r (pstrans-str (fst η)) R₀ pstrans-∙ assoc-pst-nc R₀ L₀ R₀ pstrans-∙ pstrans-whisk-l (pstrans-str (fst ε)) R₀
            ⇔
          unitl-pst-nc R₀ pstrans-∙ unitr-pst-nc R₀

  module _ {{uC : is-univ-bc-inst {{ξC}}}} {{uB : is-univ-bc-inst {{ξB}}}} where

    -- the triangulator has the following form when C and B are univalent 
    uvbiequiv-coh : (ε : (psftor-str (L ∘BC R)) psf-≃ idpfBC) (η : idpfBC psf-≃ (psftor-str (R ∘BC L))) →
      (pstrans-whisk-r (pstrans-str (fst η)) R₀ pstrans-∙ assoc-pst-nc R₀ L₀ R₀ pstrans-∙ pstrans-whisk-l (pstrans-str (fst ε)) R₀
        ⇔
      unitl-pst-nc R₀ pstrans-∙ unitr-pst-nc R₀)
        ≃  
      (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
        ≃-⇔
      unitl-psf-≃ R₀ uvpsnat-≃-∙ unitr-psf-≃ R₀)
    uvbiequiv-coh ε η = ide _

    {- For a biequivalence between univalent bicategoires, as soon as we have ζζ, we have
       a contractible choice of the remaining data of a biadjunction, i.e., the other zig-zag
       identity along with the two swallowtail identities. -}

    private

      uB-e : is-univ-bc ξB
      uB-e a b = uB {a} {b}

      uC-e : is-univ-bc ξC
      uC-e a b = uC {a} {b}

    module _ (η : idpfBC psf-≃ (psftor-str (R ∘BC L)))  where

      private
        η-i : idpfBC == psftor-str (R ∘BC L)
        η-i = ps-≃-to-== uB-e η

      biadj-zz-== : (ε : (psftor-str (L ∘BC R)) psf-≃ idpfBC) →
        (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
          ≃-⇔
        unitl-psf-≃ R₀ uvpsnat-≃-∙ unitr-psf-≃ R₀)
          ≃
        (ap (λ m → m ∘BC-s R₀) η-i ∙ ps-≃-to-== uB-e (assoc-psf-≃ R₀ L₀ R₀) ∙ ap (λ m → R₀ ∘BC-s m) (ps-≃-to-== uC-e ε)
          ==
        ps-≃-to-== uB-e (unitl-psf-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-psf-≃ R₀))
      biadj-zz-== ε =
        let
          ε-i : psftor-str (L ∘BC R) == idpfBC
          ε-i = ps-≃-to-== uC-e ε
        in
        (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R
          ≃-⇔
        unitl-psf-≃ R₀ uvpsnat-≃-∙ unitr-psf-≃ R₀)
          ≃⟨ ps-≃-InvMod-==-≃ ⁻¹ ⟩
        (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
          ==
        (unitl-psf-≃ R₀ uvpsnat-≃-∙ unitr-psf-≃ R₀)
          ≃⟨ ap-equiv ((ps-≃-==-≃ uB-e)⁻¹) _ _ ⟩
        (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
          ==
        ps-≃-to-== uB-e (unitl-psf-≃ R₀ uvpsnat-≃-∙ unitr-psf-≃ R₀))
          ≃⟨ post∙-equiv (psnat-≃-∙-pres uB-e (unitl-psf-≃ R₀) (unitr-psf-≃ R₀)) ⟩
        (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀ uvpsnat-≃-∙ assoc-psf-≃ R₀ L₀ R₀ uvpsnat-≃-∙ uvpsnat-≃-whisk-l ε R)
          ==
        ps-≃-to-== uB-e (unitl-psf-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-psf-≃ R₀))
          ≃⟨ pre∙-equiv (! (psnat-≃-∙-pres-tri uB-e
               (uvpsnat-≃-whisk-r η R₀) (assoc-psf-≃ R₀ L₀ R₀) (uvpsnat-≃-whisk-l ε R))) ⟩
        (ps-≃-to-== uB-e (uvpsnat-≃-whisk-r η R₀) ∙
        ps-≃-to-== uB-e (assoc-psf-≃ R₀ L₀ R₀) ∙
        ps-≃-to-== uB-e (uvpsnat-≃-whisk-l ε R)
          ==
        ps-≃-to-== uB-e (unitl-psf-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-psf-≃ R₀))
          ≃⟨ pre∙-equiv (! (ap2 (λ p₁ p₂ → p₁ ∙ ps-≃-to-== uB-e (assoc-psf-≃ R₀ L₀ R₀) ∙ p₂)
               (psnat-≃-whisk-r-pres uB-e η R₀)
               (psnat-≃-whisk-l-pres uC-e uB-e ε R))) ⟩
        ap (λ m → m ∘BC-s R₀) η-i ∙ ps-≃-to-== uB-e (assoc-psf-≃ R₀ L₀ R₀) ∙ ap (λ m → R₀ ∘BC-s m) ε-i
          ==
        ps-≃-to-== uB-e (unitl-psf-≃ R₀) ∙ ps-≃-to-== uB-e (unitr-psf-≃ R₀) ≃∎

    abstract
      bae-rinv-cd-contr : (psftor-str (L ∘BC R)) psf-≃ idpfBC →
        (η : idpfBC psf-≃ (psftor-str (R ∘BC L))) → is-contr (psft-rinv-coh-data (L , η))
      bae-rinv-cd-contr ε η = equiv-preserves-level ((Σ-emap-r (λ eps → biadj-zz-== η eps)) ⁻¹)
        {{∙2-≃-∘-contr ((ps-≃-==-≃ uC-e)⁻¹) (nc-ps-≃-hom-cdom (L , ε , η))
          (ap (λ m → m ∘BC-s R₀) (ps-≃-to-== uB-e η)) (ps-≃-to-== uB-e (assoc-psf-≃ R₀ L₀ R₀))}}
