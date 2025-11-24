{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import Pstransf-ops
open import Pstransf-SIP

-- coherence data for a biequivalence between bicategories (which are expected to be univalent)

module Biadj where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans
open InvMod

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {L : Psfunctor {{ξB}} {{ξC}}} {R : Psfunctor {{ξC}} {{ξB}}} where

  record Biequiv-coh (ε : (psf-str (L ∘BC R)) ps-≃ idpfBC) (η : idpfBC ps-≃ (psf-str (R ∘BC L)) :
    Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bieqvcoh
    field
      -- the zig-zag triangulator (which is an invertible modification)
      ζζ : 
        pstrans-whisk-r (pstrans-forg η) R ps-≃-∙ assoc-psf R L R ps-≃-∙ pstrans-whisk-l (pstrans-forg ε) R
          ⇔
        unitl-pst R ps-≃-∙ unitr-pst R

  {- For a biequivalence between univalent bicategoires, as soon as we have ζζ, we have
     a contractible choice of the remaining data of a biadjunction, i.e., the other zig-zag
     triangulator along with the two swallowtail identities. -}
