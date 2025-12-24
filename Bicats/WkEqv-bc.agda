{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import Bicategory
open import Bicat-coher
open import Bicat-wild

module WkEqv-bc {i j} {B₀ : Type i} where

open BicatStr {{...}}

-- weak equivalence structure on a 1-cell
record Wkequiv-bc {{ξB : BicatStr j B₀}} {a b : B₀} (f : hom a b) : Type (lmax i j) where
  constructor Wk-eqv
  field
    inv : hom b a
    eta : id₁ a == inv ◻ f
    eps : id₁ b == f ◻ inv
  dom-≃ : {c : B₀} → (hom b c) ≃ (hom a c)
  dom-≃ = equiv (λ m → m ◻ f) (λ m → m ◻ inv)
    (λ m → ! (ρ m ∙ ap (λ k → m ◻ k) eta ∙ α m inv f))
    λ m → ! (ρ m ∙ ap (λ k → m ◻ k) eps ∙ α m f inv)
  -- coher-map (the first zig-zag identity) implies coher-inv (the second)
  abstract
    cohmap-to-cohinv :
      ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps →
      ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv == lamb inv ∙ ap (λ m → m ◻ inv) eta
    cohmap-to-cohinv cm = =ₛ-out $
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ m → inv ◻ m) aux ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ap (λ m → inv ◻ m) (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps)) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 3 & 1 & ∘-ap (λ m → inv ◻ m) (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ap (λ m → inv ◻ m) (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps)) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 6 & 1 & !-∘-ap (λ m → inv ◻ m) (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 6 & 1 & apCommSq◃! (λ m →
            lamb (inv ◻ m) ∙
            ap (λ k → ⟦ ξB ⟧ k ◻ ⟦ ξB ⟧ inv ◻ m) eta ∙
            ! (α inv f (inv ◻ m)) ∙
            ap (λ k → inv ◻ k) (α f inv m))
          eps ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta ∙
      ! (α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f inv (f ◻ inv))) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 6 & 1 & !-∙-seq
          (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
          ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta ◃∙
          ! (α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
          ap (λ m → inv ◻ m) (α f inv (f ◻ inv)) ◃∎) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f inv (f ◻ inv))) ◃∙
      ! (! (α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv))) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 7 & 1 & !-! (α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f inv (f ◻ inv))) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 3 & 1 & apCommSq◃ (λ m →
            lamb (m ◻ inv) ∙
            ap (λ k → ⟦ ξB ⟧ k ◻ ⟦ ξB ⟧ m ◻ inv) eta ∙
            ! (α inv f (m ◻ inv)) ∙
            ap (λ k → inv ◻ k) (α f m inv))
          eta ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      (lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ∙
      ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (inv ◻ f) inv)) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f inv (f ◻ inv))) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₑ⟨ 5 & 1 & 
          lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
          ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
          ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ◃∙
          ap (λ m → inv ◻ m) (α f (inv ◻ f) inv) ◃∎ % =ₛ-in idp ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
      ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ◃∙
      ap (λ m → inv ◻ m) (α f (inv ◻ f) inv) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (α f inv f)) ◃∙
      ap (λ m → inv ◻ m) (! (α (⟦ ξB ⟧ f ◻ inv) f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f inv (f ◻ inv))) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 8 & 4 & ap-∙2-!2◃ (λ m → inv ◻ m)
          (α f (inv ◻ f) inv) (ap (λ m → m ◻ inv) (α f inv f)) (α (⟦ ξB ⟧ f ◻ inv) f inv) (α f inv (f ◻ inv))  ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
      ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ◃∙
      ap (λ m → inv ◻ m)
        (α f (inv ◻ f) inv ∙ ap (λ m → m ◻ inv) (α f inv f) ∙ ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ∙ ! (α f inv (f ◻ inv))) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 8 & 1 & ! (ap (ap (λ m → inv ◻ m)) (=ₛ-out (pent-bc◃-rot7 inv f inv f))) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
      ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ◃∙
      ap (λ m → inv ◻ m) (! (ap (λ m → f ◻ m) (α inv f inv))) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 8 & 1 & ! (!-ap-∘ (λ m → inv ◻ m) (λ m → f ◻ m) (α inv f inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
      ! (α inv f (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv)) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ m) (α inv f inv)) ◃∙
      α inv f (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 7 & 3 & !ₛ (apCommSq◃! (λ m → α inv f m) (α inv f inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) eta ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (α inv f inv)) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 6 & 3 & !ₛ (hmtpy-nat-!◃ (λ m → ap (λ k → ⟦ ξB ⟧ m ◻ k) (α inv f inv)) eta) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      lamb (⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ id₁ _ ◻ m) (α inv f inv)) ◃∙
      ! (lamb (⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 5 & 3 & !ₛ (hmtpy-nat-∙◃! lamb (α inv f inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ∙
      ! (α inv f (id₁ _ ◻ inv)) ∙
      ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 3 & 1 & !-∙-seq
          (lamb (⟦ ξB ⟧ id₁ _ ◻ inv) ◃∙
          ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta ◃∙
          ! (α inv f (id₁ _ ◻ inv)) ◃∙
          ap (λ m → inv ◻ m) (α f (id₁ _) inv) ◃∎) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ! (! (α inv f (id₁ _ ◻ inv))) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 4 & 1 & !-! (α inv f (id₁ _ ◻ inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ id₁ _ ◻ inv) eta) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 5 & 1 & apCommSq◃! (λ m → ap (λ k → m ◻ k) (lamb inv)) eta ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → m ◻ inv) eta) ◃∙
      ap (λ m → id₁ _ ◻ m) (lamb inv) ◃∙
      ! (lamb (⟦ ξB ⟧ id₁ _ ◻ inv)) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 7 & 2 & !ₛ (homotopy-naturality-! lamb (lamb inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → m ◻ inv) eta) ◃∙
      ! (lamb inv) ◃∙
      ap (λ m → m) (lamb inv) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 8 & 1 & ap-idf (lamb inv) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → m ◻ inv) eta) ◃∙
      ! (lamb inv) ◃∙
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 7 & 2 & !-inv-l◃ (lamb inv) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → m ◻ inv) eta) ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 6 & 2 & !-inv-l◃ (ap (λ m → m ◻ inv) eta) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → m) (α inv f inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 6 & 1 & ap ! (ap-idf (α inv f inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      α inv f (id₁ _ ◻ inv) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv ◻ f ◻ m) (lamb inv)) ◃∙
      ! (α inv f inv) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 4 & 3 & !ₛ (hmtpy-nat-∙◃! (λ m → α inv f m) (lamb inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ! (ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ m) (lamb inv)) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 4 & 1 & ap ! (ap-∘ (λ m → inv ◻ m) (λ m → f ◻ m) (lamb inv)) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → m ◻ inv) (ρ f)) ◃∙
      ! (ap (λ m → inv ◻ m) (α f (id₁ _) inv)) ◃∙
      ! (ap (λ m → inv ◻ m) (ap (λ m → f ◻ m) (lamb inv))) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 2 & 3 & !ₛ (ap-∙!!◃ (λ m → inv ◻ m)
          (ap (λ m → m ◻ inv) (ρ f)) (α f (id₁ _) inv) (ap (λ m → f ◻ m) (lamb inv))) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      ap (λ m → inv ◻ m)
        (ap (λ m → m ◻ inv) (ρ f) ∙ ! (α f (id₁ _) inv) ∙ ! (ap (λ m → f ◻ m) (lamb inv))) ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 2 & 1 & ap (ap (λ m → inv ◻ m)) (! (=ₛ-out (tri-bc◃-rot3-pre inv f))) ⟩
      ρ inv ◃∙
      ap (λ m → inv ◻ m) eps ◃∙
      idp ◃∙
      ! (ap (λ m → inv ◻ m) eps) ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 1 & 3 & !-inv-r (ap (λ m → inv ◻ m) eps) ⟩
      ρ inv ◃∙
      idp ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _)) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 1 & 2 & assoc-∙3
          (lamb (⟦ ξB ⟧ inv ◻ id₁ _)) (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta) (! (α inv f (inv ◻ id₁ _))) ⟩
      ρ inv ◃∙
      ((lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _))) ∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₑ⟨ 1 & 1 &
        (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
        ! (α inv f (inv ◻ id₁ _))) ◃∙
        ap (λ m → inv ◻ m) (α f inv (id₁ _)) ◃∎ % =ₛ-in idp ⟩
      ρ inv ◃∙
      (lamb (⟦ ξB ⟧ inv ◻ id₁ _) ∙
      ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv ◻ id₁ _) eta ∙
      ! (α inv f (inv ◻ id₁ _))) ◃∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _)) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 1 & 1 & apCommSq2◃ (λ k → lamb k ∙ ap (λ m → m ◻ k) eta ∙ ! (α inv f k)) (ρ inv) ⟩
      ρ inv ◃∙
      ! (ap (λ m → m) (ρ inv)) ◃∙
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      ap (λ m → ⟦ ξB ⟧ inv ◻ ⟦ ξB ⟧ f ◻ m) (ρ inv) ◃∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _)) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (λ m → inv ◻ m) (λ m → f ◻ m) (ρ inv)  ⟩
      ρ inv ◃∙
      ! (ap (λ m → m) (ρ inv)) ◃∙
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → f ◻ m) (ρ inv)) ◃∙
      ap (λ m → inv ◻ m) (α f inv (id₁ _)) ◃∙
      ap (λ m → inv ◻ m) (! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 3 & 3 & ∙∙-ap◃ (λ m → inv ◻ m) (ap (λ m → f ◻ m) (ρ inv)) (α f inv (id₁ _)) (! (ρ (f ◻ inv))) ⟩
      ρ inv ◃∙
      ! (ap (λ m → m) (ρ inv)) ◃∙
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      ap (λ m → inv ◻ m) (ap (λ m → f ◻ m) (ρ inv) ∙ α f inv (id₁ _) ∙ ! (ρ (f ◻ inv))) ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 3 & 1 & ap (ap (λ m → inv ◻ m)) (=ₛ-out (trig-ρ-bc-rot2 f inv)) ⟩
      ρ inv ◃∙
      ! (ap (λ m → m) (ρ inv)) ◃∙
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      idp ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 0 & 2 & !-ap-idf-r◃ (ρ inv) ⟩
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      idp ◃∙
      α inv f inv ◃∎
        =ₑ⟨ 0 & 2 & (lamb inv ◃∙ ap (λ m → m ◻ inv) eta ◃∙ ! (α inv f inv) ◃∎) % =ₛ-in $
          ∙-unit-r (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ⟩
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (α inv f inv) ◃∙
      α inv f inv ◃∎
        =ₛ⟨ 2 & 2 & !-inv-l◃ (α inv f inv) ⟩
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∎ ∎ₛ
      
      where abstract
      
        cm-rot : ap (λ m → m ◻ f) eps == ! (lamb f) ∙ ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f
        cm-rot = ! (=ₛ-out lemma)
          where
            lemma :
              ! (lamb f) ◃∙ ρ f ◃∙ ap (λ m → f ◻ m) eta ◃∙ α f inv f ◃∎
                =ₛ
              ap (λ m → m ◻ f) eps ◃∎
            lemma = 
              ! (lamb f) ◃∙ ρ f ◃∙ ap (λ m → f ◻ m) eta ◃∙ α f inv f ◃∎
                =ₛ⟨ pre-rotate'-in (=ₛ-in cm) ⟩
              ap (λ m → m ◻ f) eps ◃∎ ∎ₛ
          
        aux :
          eps ◃∎
            =ₛ
          eps ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
        aux =
          eps ◃∎
            =ₛ⟨ =ₛ-in (equiv-adj (ap-equiv dom-≃ _ _) cm-rot) ⟩
          ! (! (ρ (id₁ b) ∙ ap (λ m → id₁ b ◻ m) eps ∙ α (id₁ b) f inv)) ◃∙
          ap (λ m → m ◻ inv) (! (lamb f) ∙ ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f) ◃∙
          ! (ρ (f ◻ inv) ∙ ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps ∙ α (f ◻ inv) f inv) ◃∎
            =ₛ⟨ 2 & 1 & !-∙-seq (ρ (f ◻ inv) ◃∙ ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps ◃∙ α (f ◻ inv) f inv ◃∎) ⟩
          ! (! (ρ (id₁ b) ∙ ap (λ m → id₁ b ◻ m) eps ∙ α (id₁ b) f inv)) ◃∙
          ap (λ m → m ◻ inv) (! (lamb f) ∙ ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ⟨ 1 & 1 & ap-!-∙2-ap◃ (λ m → m ◻ inv) (λ m → f ◻ m) (lamb f) (ρ f) eta (α f inv f) ⟩
          ! (! (ρ (id₁ b) ∙ ap (λ m → id₁ b ◻ m) eps ∙ α (id₁ b) f inv)) ◃∙
          ! (ap (λ m → m ◻ inv) (lamb f)) ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ₁⟨ 0 & 1 & !-! (ρ (id₁ b) ∙ ap (λ m → id₁ b ◻ m) eps ∙ α (id₁ b) f inv) ⟩
          (ρ (id₁ b) ∙ ap (λ m → id₁ b ◻ m) eps ∙ α (id₁ b) f inv) ◃∙
          ! (ap (λ m → m ◻ inv) (lamb f)) ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₑ⟨ 0 & 1 & (ρ (id₁ b) ◃∙ ap (λ m → id₁ b ◻ m) eps ◃∙ α (id₁ b) f inv ◃∎) % =ₛ-in idp ⟩
          ρ (id₁ b) ◃∙
          ap (λ m → id₁ b ◻ m) eps ◃∙
          α (id₁ b) f inv ◃∙
          ! (ap (λ m → m ◻ inv) (lamb f)) ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ₁⟨ 0 & 1 & ! lamb-ρ-id₁-bc ⟩
          lamb (id₁ b) ◃∙
          ap (λ m → id₁ b ◻ m) eps ◃∙
          α (id₁ b) f inv ◃∙
          ! (ap (λ m → m ◻ inv) (lamb f)) ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ⟨ 0 & 2 & !ₛ (homotopy-naturality _ _ lamb eps) ⟩
          ap (λ m → m) eps ◃∙
          lamb (f ◻ inv) ◃∙
          α (id₁ b) f inv ◃∙
          ! (ap (λ m → m ◻ inv) (lamb f)) ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ⟨ 1 & 3 & !ₛ (trig-lamb-bc-rot2-pre f inv) ⟩
          ap (λ m → m) eps ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎
            =ₛ₁⟨ 0 & 1 & ap-idf eps ⟩
          eps ◃∙
          ap (λ m → m ◻ inv) (ρ f) ◃∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ inv) eta ◃∙
          ap (λ m → m ◻ inv) (α f inv f) ◃∙
          ! (α (⟦ ξB ⟧ f ◻ inv) f inv) ◃∙
          ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv ◻ m) eps) ◃∙
          ! (ρ (f ◻ inv)) ◃∎ ∎ₛ

WkEquiv-bc : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
WkEquiv-bc ξB a b = Σ (hom {{ξB}} a b) (λ f → Wkequiv-bc {{ξB}} f)
