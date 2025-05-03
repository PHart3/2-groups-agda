{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEq
open import Biequiv
open import lib.wild-cats.WildCats renaming
  (hom to homW; id₁ to id₁W; ρ to ρW; lamb to lambW; α to αW)

-- underlying wild category of bicategory

module Bicat-wild where

open BicatStr
open Adjequiv

bc-to-wc : ∀ {i j} → Bicat j i → WildCat {i} {j}
ob (bc-to-wc (B₀ , _)) = B₀
homW (bc-to-wc (_ , ξB)) = hom ξB
id₁W (bc-to-wc (_ , ξB)) = id₁ ξB
_▢_ (bc-to-wc (_ , ξB)) = _◻_ ξB
ρW (bc-to-wc (_ , ξB)) = ρ ξB
lambW (bc-to-wc (_ , ξB)) = lamb ξB
αW (bc-to-wc (_ , ξB)) h g f = ! (α ξB h g f)

module _ {i j} {B@(B₀ , ξB) : Bicat j i} where

  aeqv-to-weqv : {a b : B₀} {f : hom ξB a b} → Adjequiv {{ξB}} f → equiv-wc (bc-to-wc B) f
  fst (aeqv-to-weqv ae) = inv {{ξB}} ae
  fst (snd (aeqv-to-weqv ae)) = eta {{ξB}} ae
  snd (snd (aeqv-to-weqv ae)) = eps {{ξB}} ae

open PsfunctorStr

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

  open Pstrans
  open Nat-trans

  ptr-to-ntr : {φ₁ φ₂ : Psfunctor {{ξB}} {{ξC}}} → Pstrans φ₁ φ₂ → Nat-trans (pf-to-wf φ₁) (pf-to-wf φ₂)
  comp (ptr-to-ntr τ) = η₀ τ
  sq (ptr-to-ntr τ) = η₁ τ

module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  open BiequivStr-inst
  open Equiv-wc

  beqv-to-niso : BiequivStr ξB ξC → Equiv-wc (bc-to-wc B) (bc-to-wc C)
  ftor₁ (beqv-to-niso be) = pf-to-wf (Ψ₁ be)
  ftor₂ (beqv-to-niso be) = pf-to-wf (Ψ₂ be)
  fst (iso₁ (beqv-to-niso be)) = ptr-to-ntr (τ₁ be)
  snd (iso₁ (beqv-to-niso be)) x = aeqv-to-weqv (lev-eq₁ be x)
  fst (iso₂ (beqv-to-niso be)) = ptr-to-ntr (τ₂ be)
  snd (iso₂ (beqv-to-niso be)) x = aeqv-to-weqv (lev-eq₂ be x)

  open Psfunctor

  -- Every biequivalence is fully faithful.
  abstract
    beqv-is-ff : (be : BiequivStr ξB ξC) → {x y : B₀} → is-equiv (F₁ (str-pf (Ψ₁ be)) {x} {y})
    beqv-is-ff be = Equiv-wc-ff (beqv-to-niso be)
