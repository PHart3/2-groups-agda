{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import Bicat-wild
open import Biadj
open import Pstransf-SIP
open import Univ-bc

module Biequiv where

open BicatStr {{...}}

open import Pstransf public
open Pstrans

module _ {i₁ i₂ j₁ j₂} {C₀ : Type i₂} {B₀ : Type i₁}  where

  -- biequiv structure between two bicats
  
  record BiequivStr-inst {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}} : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bequiv
    field
      Ψ-L : Psfunctor {{ξB}} {{ξC}}
      Ψ-R : Psfunctor {{ξC}} {{ξB}}
      ε : (psftor-str (Ψ-L ∘BC Ψ-R)) ps-≃ idpfBC
      η : idpfBC ps-≃ (psftor-str (Ψ-R ∘BC Ψ-L))

    τ₁ : Pstrans (psftor-str (Ψ-L ∘BC Ψ-R)) idpfBC
    τ₁ = fst ε

    τ₂ : Pstrans idpfBC (psftor-str (Ψ-R ∘BC Ψ-L))
    τ₂ = fst η

    lev-eq₁ : (a : C₀) → Adjequiv {{ξC}} (η₀ τ₁ a)
    lev-eq₁ a = snd ε a

    lev-eq₂ : (a : B₀) → Adjequiv {{ξB}} (η₀ τ₂ a)
    lev-eq₂ a = snd η a

  -- for clarity of final theorem statement
  BiequivStr : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → Type (lmax (lmax i₁ j₁) (lmax i₂ j₂))
  BiequivStr ξC ξB = BiequivStr-inst {{ξC}} {{ξB}}

  -- biadjoint biequivalences (between univalent bicategories)
  infixr 70 _biadj-bieqv_
  _biadj-bieqv_ : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → {{is-univ-bc-inst {{ξC}}}} → {{is-univ-bc-inst {{ξB}}}}
    → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  ξC biadj-bieqv ξB = Σ (BiequivStr ξC ξB) (λ be →
    Biequiv-coh {{ξC}} {{ξB}} {L = Ψ-L {{ξC}} {{ξB}} be} {R = Ψ-R {{ξC}} {{ξB}} be} (ε {{ξC}} {{ξB}} be) (η {{ξC}} {{ξB}} be))
      where open BiequivStr-inst

module _ {i₁ i₂ j₁ j₂} {C@(C₀ , _) : Bicat j₂ i₂} {B@(B₀ , _) : Bicat j₁ i₁} where

  private
    instance
      ξC : BicatStr j₂ C₀
      ξC = snd C
      ξB : BicatStr j₁ B₀
      ξB = snd B
      
  open BiequivStr-inst
  open Equiv-wc

  -- every biequivalence induces an equivalence of wild categories
  beqv-to-wniso : BiequivStr ξC ξB → Equiv-wc (bc-to-wc B) (bc-to-wc C)
  ftor₁ (beqv-to-wniso be) = pf-to-wf (psftor-str (Ψ-L be))
  ftor₂ (beqv-to-wniso be) = pf-to-wf (psftor-str (Ψ-R be))
  fst (iso₁ (beqv-to-wniso be)) = ptr-to-ntr (τ₁ be)
  snd (iso₁ (beqv-to-wniso be)) x = aeqv-to-weqv (lev-eq₁ be x)
  fst (iso₂ (beqv-to-wniso be)) = ptr-to-ntr (τ₂ be)
  snd (iso₂ (beqv-to-wniso be)) x = aeqv-to-weqv (lev-eq₂ be x)

  module _ {{_ : is-univ-bc-inst {{ξB}}}} {{_ : is-univ-bc-inst {{ξC}}}} where

    open Psfunctor
    open PsfunctorStr
    open HAdjEquiv-wc
    open Biequiv-coh
    open InvMod

    baeqv-to-wniso : ξC biadj-bieqv ξB → HAdjEquiv-wc (bc-to-wc B) (bc-to-wc C)
    𝔼 (baeqv-to-wniso (be , _)) = beqv-to-wniso be
    zig-zag (baeqv-to-wniso (be , ba)) x =
      ap (λ m → m ◻ η₀ (τ₂ be) (map-pf (Ψ-R be) x)) (ρ ξB (F₁ (str-pf (Ψ-R be)) (η₀ (τ₁ be) x)))  ∙
      η₀-∼ (ζζ ba) x ∙
      ! (lamb ξB (id₁ ξB (map-pf (Ψ-R be) x)))

    -- Both pseudofunctors of a biadjoint biequivalence are fully faithful.
    
    baeqv-is-ff-R : ((be , _) : ξC biadj-bieqv ξB) → (x y : C₀) → is-equiv (F₁ (str-pf (Ψ-R be)) {x} {y})
    baeqv-is-ff-R bae _ _ = HAEquiv-wc-ff-R {C = bc-to-wc B} {D = bc-to-wc C} (baeqv-to-wniso bae)

    baeqv-is-ff-L : ((be , _) : ξC biadj-bieqv ξB) → (x y : B₀) → is-equiv (F₁ (str-pf (Ψ-L be)) {x} {y})
    baeqv-is-ff-L bae _ _ = HAEquiv-wc-ff-L {C = bc-to-wc B} {D = bc-to-wc C} (baeqv-to-wniso bae)

    open import Bicat-iso
{-
    is-biadj-bieqv R = ?

    -- being a biadjoint biequivalence is a mere proposition
    abstract
      biadjequiv-is-prop : is-prop (is-biadj-bieqv R)
      biadjequiv-is-prop = ?

    is-biadj-bieqv-tot = Σ ? is-biadj-bieqv

    ξC biadj-bieqv ξB ≃ is-biadj-bieqv-tot ξC ξB

    is-biadj-bieqv-tot ξC ξB ≃ ξC iso-bc ξB

    ξC biadj-bieqv ξB ≃ ξC iso-bc ξB

    ξC biadj-bieqv ξB ≃ (C == B)

  baequiv-to-==-R : is-univ-bc {{ξC}} → is-univ-bc {{ξB}} → ξC biadj-bieqv ξB → C == B
  baequiv-to-==-R uC uB = ?

  baequiv-to-==-L : is-univ-bc {{ξB}} → is-univ-bc {{ξC}} → ξB biadj-bieqv ξC → B == C
  baequiv-to-==-L uC uB = ?
-}
