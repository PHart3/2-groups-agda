{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.FTID
open import lib.types.Sigma
open import Bicategory
open import Bicat-coher
open import AdjEqv
open import Univ-bc

module AdjEqv-SIP where

open BicatStr {{...}}

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} {a b : B₀} {α₁ : AdjEquiv ξB a b} where

  AdjEqv=-contr : is-contr (Σ (AdjEquiv ξB a b) (λ α₂ → =Σ α₁ α₂))
  AdjEqv=-contr = equiv-preserves-level (Σ-emap-r (λ α₂ → (=Σ-econv α₁ α₂)⁻¹))

  AdjEqv=-ind : ∀ {k} (P : (α₂ : AdjEquiv ξB a b) → (=Σ α₁ α₂ → Type k))
    → P α₁ (idp , idp) → {α₂ : AdjEquiv ξB a b} (e : =Σ α₁ α₂) → P α₂ e
  AdjEqv=-ind P = ID-ind-map P AdjEqv=-contr

  AdjEqv=-ind-β : ∀ {k} (P : (α₂ : AdjEquiv ξB a b) → (=Σ α₁ α₂ → Type k))
    → (r : P α₁ (idp , idp)) → AdjEqv=-ind P r (idp , idp) == r
  AdjEqv=-ind-β P = ID-ind-map-β P AdjEqv=-contr

  AdjEqv=-to-== : {α₂ : AdjEquiv ξB a b} → =Σ α₁ α₂ → α₁ == α₂ 
  AdjEqv=-to-== (h₀ , h₁) = pair= h₀ h₁

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} {a b c : B₀} where

  open import WkEqv-bc-ops

  abstract

    AdjEqv-whisk-l : {α₁ α₂ : AdjEquiv ξB a b} (h : =Σ α₁ α₂) (α : AdjEquiv ξB b c) →
      ap (λ m → α AdjEqv-∘ m) (AdjEqv=-to-== h) == AdjEqv=-to-== (ap (λ m → fst α ◻ m) (fst h) , prop-has-all-paths-↓)
    AdjEqv-whisk-l {α₁} = AdjEqv=-ind
      (λ α₂ h → ∀ α → ap (λ m → α AdjEqv-∘ m) (AdjEqv=-to-== h) == AdjEqv=-to-== (ap (λ m → fst α ◻ m) (fst h) , prop-has-all-paths-↓))
      λ α → ! (ap AdjEqv=-to-== (pair= idp (prop-has-all-paths _ _))) 

    AdjEqv-whisk-r : {α₁ α₂ : AdjEquiv ξB a b} (h : =Σ α₁ α₂) (α : AdjEquiv ξB c a) →
      ap (λ m → m AdjEqv-∘ α) (AdjEqv=-to-== h) == AdjEqv=-to-== (ap (λ m → m ◻ fst α) (fst h) , prop-has-all-paths-↓)
    AdjEqv-whisk-r {α₁} = AdjEqv=-ind
      (λ α₂ h → ∀ α → ap (λ m → m AdjEqv-∘ α) (AdjEqv=-to-== h) == AdjEqv=-to-== (ap (λ m → m ◻ fst α) (fst h) , prop-has-all-paths-↓))
      λ α → ! (ap AdjEqv=-to-== (pair= idp (prop-has-all-paths _ _))) 
