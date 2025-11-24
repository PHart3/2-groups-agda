{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import Bicategory
open import Biequiv
open import AdjEq
open import Biadj
open import Bicat-iso
open import Bicat-wild
open import Univ-bc

-- quasi-univalent (2,1)-categories

module Bicat-quniv where

open BicatStr

is-quniv-bc : ∀ {i j} {B₀ : Type i} (ξB : BicatStr j B₀) → Type (lmax i j)
is-quniv-bc {B₀ = B₀} ξB = {a b : B₀} → AdjEquiv ξB a b → a == b 

univ-to-quniv : ∀ {i j} {B₀ : Type i} {ξB : BicatStr j B₀} → is-univ-bc ξB → is-quniv-bc ξB
univ-to-quniv u = is-equiv.g (u _ _) 

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
    fst (biequiv-to-iso (bequiv Ψ₁ Ψ₂ (τ₁ , lev-eq₁) (τ₂ , lev-eq₂))) = Ψ₁
    fst (snd (biequiv-to-iso (bequiv Ψ₁ Ψ₂ (τ₁ , lev-eq₁) (τ₂ , lev-eq₂)))) = is-eq (map-pf Ψ₁) (map-pf Ψ₂)
      (λ c → quC (η₀ τ₁ c , lev-eq₁ c)) λ b → ! (quB ((η₀ τ₂ b) , (lev-eq₂ b))) 
    snd (snd (biequiv-to-iso be)) x y = beqv-is-ff be {x} {y} 

    -- A biequivalence between quasi-univalent bicats implies they are equal.
    biequiv-to-== : BiequivStr ξB ξC → B == C
    biequiv-to-== = iso-bc-to-== ∘ biequiv-to-iso

    -- more coherent variant

    open BiequivStr-inst
    
    baequiv-to-iso : (be : BiequivStr ξB ξC) → Biequiv-coh (ε be) (η be) → ξB iso-bc ξC
    fst (baequiv-to-iso be _) = fst (biequiv-to-iso be)
    fst (snd (baequiv-to-iso be _)) = fst (snd (biequiv-to-iso be))
    snd (snd (baequiv-to-iso be ba)) x y = baeqv-is-ff be ba {x} {y} 

    beequiv-to-== : (be : BiequivStr ξB ξC) → Biequiv-coh (ε be) (η be) → B == C
    beequiv-to-== be ba = iso-bc-to-== (baequiv-to-iso be ba)
