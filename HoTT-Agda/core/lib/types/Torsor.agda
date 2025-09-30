{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.Truncation
open import lib.types.TLevel
open import lib.types.PtdFibration

-- the type of torsors over an arbitrary pointed type

module lib.types.Torsor where

Torsors : ({i} j : ULevel) (X : Ptd i) → Type (lmax i (lsucc j))
Torsors j X = [ Y ∈ Type j ] × Trunc -1 Y × Π Y (λ y → X ⊙≃ ⊙[ Y , y ]) 

Torsor-pr22 : ∀ {i j} {X : Ptd i} (T : Torsors j X)
  → Π (fst T) (λ y → X ⊙≃ ⊙[ fst T , y ])
Torsor-pr22 T = snd (snd T)

PtdTorsors : ({i} j : ULevel) (X : Ptd i) → Type (lmax i (lsucc j))
PtdTorsors j X = Σ (Torsors j X) fst

PtdTorsor-pr1 : ∀ {i j} {X : Ptd i} → PtdTorsors j X → Type j
PtdTorsor-pr1 T = fst (fst T)

module _ {i : ULevel} (X*@(⊙[ X , x₀ ]) : Ptd i) where

  PtdTorsors-alt : PtdTorsors i X* ≃ [ μ ∈ Π X (λ x → X* ⊙≃ ⊙[ X , x ]) ] × (μ x₀ == ⊙ide X*)
  PtdTorsors-alt =
    [ (Y , _ , _) ∈ Torsors i X* ] × Y
      ≃⟨ equiv (λ ((Y , h , μ) , y) → ⊙[ Y , y ] , μ) (λ (Z* , μ) → ((de⊙ Z*) , ([ pt Z* ] , μ)) , (pt Z*))
           (λ _ → idp)
           (λ ((Y , h , μ) , y) → ap (λ h → (_ , (h , μ)) , _) (prop-has-all-paths _ _) ) ⟩
    [ (⊙[ Z , _ ]) ∈ Ptd i ] × Π Z (λ z → X* ⊙≃ ⊙[ Z , z ])
      ≃⟨ Σ-emap-r {A = Ptd i} (λ (⊙[ Z , z₀ ]) → (Σ-contr-red-cod {A = Π Z (λ z → X* ⊙≃ ⊙[ Z , z ])}) ⁻¹) ⟩
    [ Z*@(⊙[ Z , z₀ ]) ∈ Ptd i ] × [ μ ∈ Π Z (λ z → X* ⊙≃ ⊙[ Z , z ]) ] × [ p ∈ X* ⊙≃ Z* ] × (μ z₀ == p)
      ≃⟨ equiv (λ (Z* , μ , p , e) → (Z* , p) , (μ , e)) (λ ((Z* , p) , (μ , e)) → Z* , (μ , (p , e))) (λ _ → idp) (λ _ → idp) ⟩
    [ ((⊙[ Z , z₀ ]) , p) ∈ Σ (Ptd i) (λ Z* → X* ⊙≃ Z*) ] × [ μ ∈ Π Z (λ z → X* ⊙≃ ⊙[ Z , z ]) ] × (μ z₀ == p)
      ≃⟨ Σ-contr-red ⊙≃-contr-exp ⟩
    [ μ ∈ Π X (λ x → X* ⊙≃ ⊙[ X , x ]) ] × (μ x₀ == ⊙ide X*) ≃∎

  PtdTorsors-level : {n₁ n₂ : ℕ₋₂} {{cX : is-connected (S n₁) X}} {{tX : has-level ((n₂ +2+ n₁) +2+ n₁) X}} → has-level n₂ (PtdTorsors i X*)
  PtdTorsors-level = equiv-preserves-level (PtdTorsors-alt ⁻¹)

instance
  PtdTorsors-contr : {i : ULevel} {X*@(⊙[ X , x₀ ]) : Ptd i} {n : ℕ₋₂}
    → {{cX : is-connected (S n) X}} {{tX : has-level (n +2+ n) X}} → is-contr (PtdTorsors i X*)
  PtdTorsors-contr {X* = X*} = PtdTorsors-level X* {n₂ = ⟨-2⟩}
