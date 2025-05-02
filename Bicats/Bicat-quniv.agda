{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import Bicategory
open import Biequiv
open import AdjEq
open import Bicat-iso
open import Bicat-wild

-- quasi-univalent (2,1)-categories

module Bicat-quniv where

open BicatStr

is-quniv-bc : ∀ {i j} {B₀ : Type i} (ξB : BicatStr j B₀) → Type (lmax i j)
is-quniv-bc {B₀ = B₀} ξB = {a b : B₀} → AdjEquiv ξB a b → a == b 

module _ {i j} {B@(B₀ , _) C@(C₀ , _) : Bicat j i} where

  open Psfunctor
  open PsfunctorStr
  open Pstrans

  private
    instance
      ξB : BicatStr j B₀
      ξB = snd B
      ξC : BicatStr j C₀
      ξC = snd C

  module _ (quB : is-quniv-bc ξB) (quC : is-quniv-bc ξC) where

    biequiv-to-iso : BiequivStr ξB ξC → ξB iso-bc ξC
    fst (biequiv-to-iso (bequiv Ψ₁ Ψ₂ τ₁ τ₂ lev-eq₁ lev-eq₂)) = Ψ₁
    fst (snd (biequiv-to-iso (bequiv Ψ₁ Ψ₂ τ₁ τ₂ lev-eq₁ lev-eq₂))) = is-eq (map-pf Ψ₁) (map-pf Ψ₂)
      (λ c → quC (η₀ τ₁ c , lev-eq₁ c)) λ b → ! (quB ((η₀ τ₂ b) , (lev-eq₂ b))) 
    snd (snd (biequiv-to-iso be)) x y = beqv-is-ff be {x} {y} 

    -- A biequivalence between quasi-univalent bicats implies they are equal.
    biequiv-to-== : BiequivStr ξB ξC → B == C
    biequiv-to-== = iso-bc-to-== ∘ biequiv-to-iso
