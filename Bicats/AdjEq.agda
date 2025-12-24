{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.FTID
open import lib.types.Sigma
open import lib.wild-cats.WildCat using (equiv-wc)
open import Bicategory
open import Bicat-coher
open import Bicat-wild

module AdjEq {i j} {B₀ : Type i} where

open BicatStr {{...}}

-- adjoint equivalence structure on a 1-cell of a bicategory
record Adjequiv {{_ : BicatStr j B₀}} {a b : B₀} (f : hom a b) : Type (lmax i j) where
  constructor Adj-eqv
  field
    inv : hom b a
    eta : id₁ a == inv ◻ f
    eps : id₁ b == f ◻ inv
    coher-map : ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps
    coher-inv : ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv == lamb inv ∙ ap (λ m → m ◻ inv) eta

  coher-map-◃ : ρ f ◃∙ ap (λ m → f ◻ m) eta ◃∙ α f inv f ◃∎ =ₛ lamb f ◃∙ ap (λ m → m ◻ f) eps ◃∎
  coher-map-◃ = =ₛ-in coher-map

  coher-map-rot : ap (λ m → f ◻ m) eta ◃∎ =ₛ ! (ρ f) ◃∙ lamb f ◃∙ ap (λ m → m ◻ f) eps ◃∙ ! (α f inv f) ◃∎
  coher-map-rot = pre-rotate-in (post-rotate-in coher-map-◃)

  coher-map-rot2 : ! (lamb f) ◃∙ ρ f ◃∙ ap (λ m → f ◻ m) eta ◃∙ α f inv f ◃∎ =ₛ ap (λ m → m ◻ f) eps ◃∎
  coher-map-rot2 = pre-rotate'-in coher-map-◃

  coher-inv-◃ : ρ inv ◃∙ ap (λ m → inv ◻ m) eps ◃∙ α inv f inv ◃∎ =ₛ lamb inv ◃∙ ap (λ m → m ◻ inv) eta ◃∎
  coher-inv-◃ = =ₛ-in coher-inv

  coher-inv-rot : ap (λ m → inv ◻ m) eps ◃∎ =ₛ ! (ρ inv) ◃∙ lamb inv ◃∙ ap (λ m → m ◻ inv) eta ◃∙ ! (α inv f inv) ◃∎
  coher-inv-rot = pre-rotate-in (post-rotate-in coher-inv-◃)

  coher-inv-rot2 : ! (lamb inv) ◃∙ ρ inv ◃∙ ap (λ m → inv ◻ m) eps ◃∙ α inv f inv ◃∎ =ₛ ap (λ m → m ◻ inv) eta ◃∎
  coher-inv-rot2 = pre-rotate'-in coher-inv-◃

  coher-inv-rot3 : ρ inv ◃∙ ap (λ m → inv ◻ m) eps ◃∙ α inv f inv ◃∙ ! (ap (λ m → m ◻ inv) eta) ◃∎ =ₛ lamb inv ◃∎
  coher-inv-rot3 = post-rotate'-in coher-inv-◃

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
      ap (λ m → m ◻ f) eps == ! (lamb f) ∙ ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f →
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
        =ₛ⟨ 8 & 4 & {!!}  ⟩
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
        =ₛ⟨ 2 & 3 & {!!} ⟩
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
        =ₛ₁⟨ 1 & 2 & {!!} ⟩
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
        =ₛ⟨ 3 & 3 & ? ⟩
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
        =ₛ₁⟨ 0 & 2 & !-ap-idf-r (ρ inv) ⟩
      idp ◃∙
      (lamb inv ∙ ap (λ m → m ◻ inv) eta ∙ ! (α inv f inv)) ◃∙
      idp ◃∙
      α inv f inv ◃∎
        =ₑ⟨ 0 & 2 & (lamb inv ◃∙ ap (λ m → m ◻ inv) eta ◃∙ ! (α inv f inv) ◃∎) % =ₛ-in idp ⟩
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      ! (α inv f inv) ◃∙
      idp ◃∙
      α inv f inv ◃∎
        =ₛ₁⟨ 2 & 3 & !-inv-l (α inv f inv) ⟩
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 2 & ∙-unit-r (ap (λ m → m ◻ inv) eta) ⟩
      lamb inv ◃∙
      ap (λ m → m ◻ inv) eta ◃∎ ∎ₛ
      
      where abstract
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
            =ₛ⟨ =ₛ-in (equiv-adj (ap-equiv dom-≃ _ _) cm) ⟩
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

{-
open Adjequiv
open Wkequiv-bc

AdjEquiv : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
AdjEquiv ξB a b = Σ (hom {{ξB}} a b) (λ f → Adjequiv {{ξB}} f)

WkEquiv-bc : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
WkEquiv-bc ξB a b = Σ (hom {{ξB}} a b) (λ f → Wkequiv-bc {{ξB}} f)

-- some basic operations on equivalences

module _ {{ξB : BicatStr j B₀}} where

  adjeqv-frg : {a b : B₀} → AdjEquiv ξB a b → WkEquiv-bc ξB a b
  fst (adjeqv-frg (f , ae)) = f
  snd (adjeqv-frg (f , ae)) = Wk-eqv (inv ae) (eta ae) (eps ae)

  module _ {a b : B₀} ((f , we) : WkEquiv-bc ξB a b) where

    abstract

      wkeqv-refine0 :
        ρ f ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        α f (inv we) f ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine0 = 
        ρ f ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        α f (inv we) f ◃∎
          =ₛ⟨ =ₛ-in (! (ap-idf-idp (ρ f ∙  ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f))) ⟩
        ap (λ m → m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        idp ◃∎
          =ₛ⟨ 1 & 1 & =ₛ-in (=ₛ-out (trig-lamb-bc-rot2 (f ◻ inv we) f)) ⟩
        ap (λ m → m) (ρ f ∙  ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        lamb (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 0 & 2 & homotopy-naturality _ _ lamb (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 0 & 1 & (lamb f ◃∙ idp ◃∎) % =ₛ-in (! (∙-unit-r (lamb f))) ⟩
        lamb f ◃∙
        idp ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 1 & 1 & (ap (λ m → m ◻ f) (eps we) ◃∙ idp ◃∙ ! (ap (λ m → m ◻ f) (eps we)) ◃∎)
            % =ₛ-in (! (!-inv-r (ap (λ m → m ◻ f) (eps we)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        idp ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 2 & 1 & (! (α f (inv we) f) ◃∙ idp ◃∙ idp ◃∙ α f (inv we) f ◃∎) % =ₛ-in (! (!-inv-l (α f (inv we) f))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        idp ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 4 & 1 & (ap (λ m → f ◻ m) (ρ (inv we ◻ f) ∙ ! (α (inv we) f (id₁ _)) ∙ ! (ap (λ m → inv we ◻ m) (ρ f))) ◃∎)
            % =ₛ-in (ap (ap (λ m → f ◻ m)) (! (=ₛ-out (trig-ρ-bc-rot-pre (inv we) f)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙ ! (α (inv we) f (id₁ _)) ∙ ! (ap (λ m → inv we ◻ m) (ρ f))) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 4 & 1 & ap-∙!!ap◃ (λ m → f ◻ m) (λ m → inv we ◻ m) (ρ (inv we ◻ f)) (α (inv we) f (id₁ _)) (ρ f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → inv we ◻ m) (ρ f))) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & ap ! (∘-ap (λ m → f ◻ m) (λ m → inv we ◻ m) (ρ f)) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ m) (ρ f)) ◃∙
        α f (inv we) f ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 6 & 2 & !ₛ (homotopy-naturality-!ap (λ m → α f (inv we) m) (ρ f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        idp ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 3 & 1 &
            (ap (λ m → f ◻ m)
              (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∎)
            % =ₛ-in (ap (ap (λ m → f ◻ m)) (! (=ₛ-out (trig-lamb-bc-rot (inv we) f)))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine1 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine1 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m)
          (ap (λ m → m ◻ f) (lamb (inv we)) ∙ ! (α (id₁ _) (inv we) f) ∙ ! (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 1 & ap-∙ap!!◃ (λ m → f ◻ m) (λ m → m ◻ f)
            (lamb (inv we)) (α (id₁ _) (inv we) f) (lamb (⟦ ξB ⟧ inv we ◻ f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → m ◻ f) (lamb (inv we))) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 3 & 1 & ∘-ap (λ m → f ◻ m) (λ m → m ◻ f) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ! (α f (inv we) f) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ f) (lamb (inv we)) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 2 & 2 & homotopy-naturality-! (λ m → α f m f) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ m ◻ f) (lamb (inv we)) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-∘ (λ m → m ◻ f) (λ m → f ◻ m) (lamb (inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ◃∙
        α f (inv we) (f ◻ id₁ _) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 7 & 2 & (! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ∙ α f (inv we) (f ◻ id₁ _)) ◃∎ % =ₛ-in idp ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        (! (ap (λ m → f ◻ m) (α (inv we) f (id₁ _))) ∙ α f (inv we) (f ◻ id₁ _)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 7 & 1 &
            apCommSq2◃-rev (λ k → ! (ap (λ m → f ◻ m) (α (inv we) f k)) ∙ α f (inv we) (⟦ ξB ⟧ f ◻ k)) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        (! (ap (λ m → f ◻ m) (α (inv we) f (inv we ◻ f))) ∙ α f (inv we) (⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 8 & 1 &
            (α f (inv we ◻ f) (inv we ◻ f) ◃∙
            ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
            idp ◃∙
            ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∎)
            % =ₛ-in (=ₛ-out (pent-bc◃-rot6 (inv we ◻ f) f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine2 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine2 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        idp ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 10 & 1 &
            (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙ ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∎)
            % =ₛ-in (! (!-inv-r (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f))) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        α f (inv we ◻ f) (inv we ◻ f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 8 & 1 & pent-bc◃-rot5 f (inv we) (inv we ◻ f) f ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ! (α (⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ inv we ◻ f) (inv we) f) ◃∙
        ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ inv we ◻ f) (α f (inv we) f) ◃∙
        α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 11 & 3 & !ₛ (apCommSq◃ (λ m → α m (inv we) f) (α f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ inv we ◻ f) (α f (inv we) f) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 11 & 1 & ap-∘ (λ m → m ◻ f) (λ m → m ◻ inv we) (α f (inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (α f (inv we ◻ f) (inv we)) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → m ◻ inv we) (α f (inv we) f)) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 10 & 2 & ap-seq-=ₛ (λ m → m ◻ f) (!ₛ (pent-bc◃-rot4 (inv we) f (inv we) f)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ap (λ m → m ◻ f) (α (f ◻ inv we) f (inv we)) ◃∙
        ! (α (⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ f) (inv we) f) ◃∙
        ! (α (f ◻ inv we) f (inv we ◻ f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 12 & 3 & !ₛ (pent-bc◃-rot3 f (inv we) f (f ◻ inv we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine3 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine3 = 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 7 & 1 & ap-∘ (λ m → f ◻ m) (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we)) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ ⟦ ξB ⟧ f ◻ m) (eta we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 14 & 1 & ap ! (ap-∘ (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (λ m → f ◻ m) (eta we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        ap (λ m → f ◻ m) (ρ (inv we ◻ f)) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we)) ◃∙
        ap (λ m → f ◻ m) (α (inv we ◻ f) (inv we) f) ◃∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ap (λ m → f ◻ m) (eta we))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 6 & 4 & ap-∙-ap-∙◃ (λ m → f ◻ m) (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m)
            (ρ (inv we ◻ f)) (eta we) (α (inv we ◻ f) (inv we) f) (α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (α (f ◻ inv we) (f ◻ inv we) f) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (α f (inv we) f)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ap (λ m → f ◻ m) (eta we))) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 9 & 4 & !-ap-∙-ap-∙2◃ (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (λ m → f ◻ m)
            (ρ f) (eta we) (α f (inv we) f) (α (f ◻ inv we) (f ◻ inv we) f) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine4 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine4 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ◃∙
        α (id₁ _) (f ◻ inv we) f ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₑ⟨ 11 & 2 &
            (ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙ α (id₁ _) (f ◻ inv we) f) ◃∎
            % =ₛ-in idp ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        (! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ inv we ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (f ◻ inv we) (f ◻ inv we) f)) ◃∙
        ! (ap (λ m → m ◻ f) (eps we)) ◃∙
        (ap (λ m → id₁ _ ◻ m) (ρ f ∙ ap (λ m → f ◻ m) (eta we) ∙ α f (inv we) f) ∙
        α (id₁ _) (f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 9 & 3 & !ₛ (apCommSq◃!
            (λ m → ap (λ k → m ◻ k) (ρ f ∙ ap (λ k → f ◻ k) (eta we) ∙ α f (inv we) f) ∙ α m (f ◻ inv we) f)
            (eps we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (⟦ ξB ⟧ inv we ◻ f))) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 5 & 1 & apCommSq2◃!-ap lamb (eta we) (λ m → f ◻ m) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (ap (λ m → m) (eta we)) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 7 & 1 & ap (ap (λ m → f ◻ m)) (ap-idf (eta we)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

      wkeqv-refine5 :
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ
        lamb f ◃∙
        ap (λ m → m ◻ f)
          (eps we ∙
          ap (λ m → f ◻ m) (lamb (inv we)) ∙
          ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ∙
          ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
          α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ∙
          ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
          ! (lamb (f ◻ inv we))) ◃∎
      wkeqv-refine5 =
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (lamb (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & ap ! (ap (ap (λ m → f ◻ m)) lamb-ρ-id₁-bc) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ! (α f (id₁ _ ◻ inv we) f) ◃∙
        ! (ap (λ m → f ◻ m) (α (id₁ _) (inv we) f)) ◃∙
        ! (ap (λ m → f ◻ m) (ap (λ m → id₁ _ ◻ m) (eta we))) ◃∙
        ! (ap (λ m → f ◻ m) (ρ (id₁ _))) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 4 & !-ap-∙-ap-∙2◃ (λ m → f ◻ m) (λ m → id₁ _ ◻ m)
            (ρ (id₁ _)) (eta we) (α (id₁ _) (inv we) f) (α f (id₁ _ ◻ inv we) f) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        (! (ap (λ m → f ◻ m) (ρ (id₁ _) ∙ ap (λ m → id₁ _ ◻ m) (eta we) ∙ α (id₁ _) (inv we) f) ∙
        α f (id₁ _ ◻ inv we) f)) ◃∙
        ap (λ m → f ◻ m) (eta we) ◃∙
        (ap (λ m → f ◻ m)
          (ρ (inv we ◻ f) ∙
          ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ m) (eta we) ∙
          α (inv we ◻ f) (inv we) f) ∙
        α f (⟦ ξB ⟧ ⟦ ξB ⟧ inv we ◻ f ◻ inv we) f) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 3 & 3 & !ₛ $
            apCommSq◃
              (λ m → ap (λ k → f ◻ k) (ρ m ∙ ap (λ k → m ◻ k) (eta we) ∙ α m (inv we) f) ∙ α f (m ◻ inv we) f)
              (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we ◻ f) (eta we) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-∘ (λ m → m ◻ f) (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ! (ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we ◻ f) (eps we)) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ₁⟨ 6 & 1 & !-ap-∘ (λ m → m ◻ f) (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we) ⟩ 
        lamb f ◃∙
        ap (λ m → m ◻ f) (eps we) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → f ◻ m) (lamb (inv we))) ◃∙
        ap (λ m → m ◻ f) (ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → f ◻ m) (α (inv we) f (inv we)))) ◃∙
        ap (λ m → m ◻ f) (α f (inv we) (⟦ ξB ⟧ f ◻ inv we)) ◃∙
        ap (λ m → m ◻ f) (! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we))) ◃∙
        ap (λ m → m ◻ f) (! (lamb (f ◻ inv we))) ◃∎
          =ₛ⟨ 1 & 7 & !ₛ (ap-seq-∙ (λ m → m ◻ f)
            (eps we ◃∙
            ap (λ m → f ◻ m) (lamb (inv we)) ◃∙
            ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ◃∙
            ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ◃∙
            α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ◃∙
            ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ◃∙
            ! (lamb (f ◻ inv we)) ◃∎)) ⟩
        lamb f ◃∙
        ap (λ m → m ◻ f)
          (eps we ∙
          ap (λ m → f ◻ m) (lamb (inv we)) ∙
          ap (λ m → ⟦ ξB ⟧ f ◻ ⟦ ξB ⟧ m ◻ inv we) (eta we) ∙
          ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
          α f (inv we) (⟦ ξB ⟧ f ◻ inv we) ∙
          ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
          ! (lamb (f ◻ inv we))) ◃∎ ∎ₛ

  -- every weak equivalence can be promoted to an adjoint one
  wkeqv-bc-promote : {a b : B₀} → WkEquiv-bc ξB a b → AdjEquiv ξB a b
  fst (wkeqv-bc-promote (f , we)) = f
  inv (snd (wkeqv-bc-promote (f , we))) = inv we
  eta (snd (wkeqv-bc-promote (f , we))) = eta we
  eps (snd (wkeqv-bc-promote (f , we))) =
    eps we ∙
    ap (λ m → f ◻ m) (lamb (inv we)) ∙
    ap (λ m → f ◻ m ◻ inv we) (eta we) ∙
    ! (ap (λ m → f ◻ m) (α (inv we) f (inv we))) ∙
    α f (inv we) (f ◻ inv we) ∙
    ! (ap (λ m → ⟦ ξB ⟧ m ◻ ⟦ ξB ⟧ f ◻ inv we) (eps we)) ∙
    ! (lamb (f ◻ inv we))
  coher-map (snd (wkeqv-bc-promote e)) = =ₛ-out $
    wkeqv-refine0 e ∙ₛ wkeqv-refine1 e ∙ₛ wkeqv-refine2 e ∙ₛ wkeqv-refine3 e ∙ₛ wkeqv-refine4 e ∙ₛ wkeqv-refine5 e
  coher-inv (snd (wkeqv-bc-promote (f , we))) = cohmap-to-cohinv
    (Wk-eqv (inv we) (eta we) (eps (snd (wkeqv-bc-promote (f , we)))))
    (coher-map (snd (wkeqv-bc-promote (f , we))))

  Adjequiv-whisk-r-≃ : {a b c : B₀} {f : hom a b} → Adjequiv f → (hom b c) ≃ (hom a c) 
  Adjequiv-whisk-r-≃ {f = f} ae = equiv (λ m → m ◻ f) (λ m → m ◻ inv ae)
    (λ m → ! (α m (inv ae) f) ∙ ! (ap (λ k → m ◻ k) (eta ae)) ∙ ! (ρ m))
    λ m → ! (α m f (inv ae)) ∙ ! (ap (λ k → m ◻ k) (eps ae)) ∙ ! (ρ m)

  infix 50 _WkEqv-bc-∘_
  _WkEqv-bc-∘_ : {a b c : B₀} → WkEquiv-bc ξB b c → WkEquiv-bc ξB a b → WkEquiv-bc ξB a c
  fst (g , aeg WkEqv-bc-∘ f , aef) = g ◻ f
  inv (snd (g , aeg WkEqv-bc-∘ f , aef)) = inv aef ◻ inv aeg
  eta (snd (g , aeg WkEqv-bc-∘ f , aef)) =
    eta aef ∙
    ap (λ m → m ◻ f) (ρ (inv aef)) ∙
    ap (λ m → ⟦ ξB ⟧ ⟦ ξB ⟧ inv aef ◻ m ◻ f) (eta aeg) ∙
    ap (λ m → m ◻ f) (α (inv aef) (inv aeg) g) ∙
    ! (α (inv aef ◻ inv aeg) g f) 
  eps (snd (g , aeg WkEqv-bc-∘ f , aef)) = 
    eps aeg ∙
    ap (λ m → g ◻ m) (lamb (inv aeg)) ∙
    ap (λ m → ⟦ ξB ⟧ g ◻ ⟦ ξB ⟧ m ◻ inv aeg) (eps aef) ∙
    ! (ap (λ m → g ◻ m) (α f (inv aef) (inv aeg))) ∙
    α g f (inv aef ◻ inv aeg)

  infix 50 _AdjEq-∘_
  _AdjEq-∘_ : {a b c : B₀} → AdjEquiv ξB b c → AdjEquiv ξB a b → AdjEquiv ξB a c
  g AdjEq-∘ f = wkeqv-bc-promote (adjeqv-frg g WkEqv-bc-∘ adjeqv-frg f)
  
  AdjEq-rev : {a b : B₀} → AdjEquiv ξB a b → AdjEquiv ξB b a
  fst (AdjEq-rev (f , ae)) = inv ae
  inv (snd (AdjEq-rev (f , ae))) = f
  eta (snd (AdjEq-rev (f , ae))) = eps ae
  eps (snd (AdjEq-rev (f , ae))) = eta ae
  coher-map (snd (AdjEq-rev (f , ae))) = coher-inv ae
  coher-inv (snd (AdjEq-rev (f , ae))) = coher-map ae

  AdjEq-rev-≃ : {a b : B₀} → AdjEquiv ξB a b ≃ AdjEquiv ξB b a
  AdjEq-rev-≃ = equiv AdjEq-rev AdjEq-rev (λ _ → idp) λ _ → idp

-- induced internal equivalence in underlying wild category
aeqv-to-weqv : {{ξB : BicatStr j B₀}} {a b : B₀} {f : hom {{ξB}} a b} → Adjequiv f → equiv-wc (bc-to-wc (B₀ , ξB)) f
fst (aeqv-to-weqv ae) = inv ae
fst (snd (aeqv-to-weqv ae)) = eta ae
snd (snd (aeqv-to-weqv ae)) = eps ae
-}
{-
module ae-unique {{_ : BicatStr j B₀}} {a b : B₀} {f : hom a b} where

  -- extensional equality of adjoint equivalence structures
  infix 30 _Adjeq≃_
  _Adjeq≃_ : Adjequiv f → Adjequiv f → Type j
  α₁ Adjeq≃ α₂ = [ e-inv ∈ inv α₁ == inv α₂ ] ×
    ((eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂) × (eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps α₂))

  Adjeq≃-id : (α₁ : Adjequiv f) → α₁ Adjeq≃ α₁
  Adjeq≃-id _ = idp , (idp , idp)

  abstract
    -- eta coherence of Adjeq≃ implies eps coherence
    coher-r-to-coher-l : {α₁ α₂ : Adjequiv f} (e-inv : inv α₁ == inv α₂) →
      (eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂) → (eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps α₂)
    coher-r-to-coher-l {α₁} {α₂} e-inv c = =ₛ-out $
      (eps α₁ ∙' ap (λ m → f ◻ m) e-inv) ◃∎
        =ₛ⟨ =ₛ-in (∙'=∙ (eps α₁) (ap (λ m → f ◻ m) e-inv )) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) e-inv ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ m → f ◻ m) aux2 ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (ap (λ m → m ◻ inv α₁) (eta α₂)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → f ◻ m) (λ m → m ◻ inv α₁) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      ap (λ m → f ◻ m ◻ inv α₁) (eta α₂) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃ (λ m → α f m (inv α₁)) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → (f ◻ m) ◻ inv α₁) (eta α₂) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (λ m → m ◻ inv α₁) (λ m → f ◻ m) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → f ◻ m) (eta α₂)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ m → m ◻ inv α₁) (coher-map-rot α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 9 & 1 &
          ap-! (λ m → f ◻ m) (ap (λ m → inv α₂ ◻ m) (eps α₁)) ∙
          ap ! (∘-ap (λ m → f ◻ m) (λ m → inv α₂ ◻ m) (eps α₁) ) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ! (ap (λ m → f ◻ inv α₂ ◻ m) (eps α₁)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 9 & 1 & hmtpy-nat-∙◃! (λ m → α f (inv α₂) m ∙ ! (ap (λ k → k ◻ m) (eps α₂)) ∙ ! (lamb m)) (eps α₁) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      ! (α f (inv α₂) (id₁ b) ∙
      ! (ap (λ m → m ◻ id₁ b) (eps α₂)) ∙
      ! (lamb (id₁ b))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 11 & 1 & !-∙-seq (α f (inv α₂) (id₁ b) ◃∙ ! (ap (λ m → m ◻ id₁ b) (eps α₂)) ◃∙ ! (lamb (id₁ b)) ◃∎) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      ! (! (lamb (id₁ b))) ◃∙
      ! (! (ap (λ m → m ◻ id₁ b) (eps α₂))) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₑ⟨ 11 & 2 & (lamb (id₁ b) ◃∙ ap (λ m → m ◻ id₁ b) (eps α₂) ◃∎)
          % =ₛ-in (ap2 _∙_ (!-! (lamb (id₁ b))) (!-! (ap (λ m → m ◻ id₁ b) (eps α₂)))) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      lamb (id₁ b) ◃∙
      ap (λ m → m ◻ id₁ b) (eps α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 12 & 1 & apCommSq◃ ρ (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      lamb (id₁ b) ◃∙
      ! (ρ (id₁ b)) ◃∙
      ap (λ m → m) (eps α₂) ◃∙
      ρ (f ◻ inv α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 11 & 2 & ap (λ p → p ∙ ! (ρ (id₁ b))) lamb-ρ-id₁-bc ∙ !-inv-r (ρ (id₁ b)) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∙
      ρ (f ◻ inv α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 13 & 3 & trig-ρ-bc-rot f (inv α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₑ⟨ 9 & 1 & (α f (inv α₂) (f ◻ inv α₁) ◃∙ ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙ ! (lamb (f ◻ inv α₁)) ◃∎)
          % =ₛ-in idp ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 5 & 1 & ∘-ap (λ m → m ◻ inv α₁) (λ m → m ◻ f) (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → (m ◻ f) ◻ inv α₁) (eps α₂) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 5 & 1 & apCommSq◃ (λ m → α m f (inv α₁)) (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ap (λ m → m ◻ f ◻ inv α₁) (eps α₂) ◃∙
      α (f ◻ (inv α₂)) f (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 7 & 5 & pent-bc◃-rot (inv α₁) f (inv α₂) f ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ap (λ m → m ◻ f ◻ inv α₁) (eps α₂) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 6 & 2 & !-inv-r (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      idp ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 1 & 3 & tri-bc◃-rot2 (inv α₁) f ⟩
      eps α₁ ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      idp ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 3 & 2 & idp ⟩
      eps α₁ ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 1 & 3 & trig-lamb-bc-rot f (inv α₁) ⟩
      eps α₁ ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 0 & 2 & !-ap-idf-r (eps α₁) ⟩
      idp ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ ap-idf (eps α₂) ⟩
      eps α₂ ◃∎ ∎ₛ

      where

        aux1 : ap (λ m → m ◻ f) e-inv == ! (eta α₁) ∙ eta α₂
        aux1 = ∙'-rot-out (eta α₁) (ap (λ m → m ◻ f) e-inv) c

        aux2 :
          e-inv ◃∎
            =ₛ
          lamb (inv α₁) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
        aux2 = 
          e-inv ◃∎
            =ₛ⟨ =ₛ-in (equiv-adj (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) aux1) ⟩
          ! (! (α (inv α₁) f (inv α₁)) ∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ∙ ! (ρ (inv α₁))) ◃∙
          ap (λ m → m ◻ inv α₁) (! (eta α₁) ∙ eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 1 & 1 & ap-!∙◃ (λ m → m ◻ inv α₁) (eta α₁) (eta α₂) ⟩
          ! (! (α (inv α₁) f (inv α₁)) ∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ∙ ! (ρ (inv α₁))) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 0 & 1 & !-∙-seq (! (α (inv α₁) f (inv α₁)) ◃∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ◃∙ ! (ρ (inv α₁)) ◃∎) ⟩
          ! (! (ρ (inv α₁))) ◃∙
          ! (! (ap (λ m → inv α₁ ◻ m) (eps α₁))) ◃∙
          ! (! (α (inv α₁) f (inv α₁))) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₑ⟨ 0 & 3 & (ρ (inv α₁) ◃∙ ap (λ m → inv α₁ ◻ m) (eps α₁) ◃∙ α (inv α₁) f (inv α₁) ◃∎)
              % =ₛ-in (ap3 (λ p₁ p₂ p₃ → p₁ ∙ p₂ ∙ p₃)
                (!-! (ρ (inv α₁)))
                (!-! (ap (λ m → inv α₁ ◻ m) (eps α₁)))
                (!-! (α (inv α₁) f (inv α₁)))) ⟩
          ρ (inv α₁) ◃∙
          ap (λ m → inv α₁ ◻ m) (eps α₁) ◃∙
          α (inv α₁) f (inv α₁) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 0 & 4 & coher-inv-rot3 α₁ ⟩
          lamb (inv α₁) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎ ∎ₛ

  module ae-SIP {α₁ : Adjequiv f} where

    -- SIP for adjoint equivalence structures

    Adjeq≃-contr-aux :
      is-contr $
        [ (inv₂ , e-inv) ∈ Σ (hom b a) (λ inv₂ → inv α₁ == inv₂) ] ×
          [ ((eta₂ , _) , eps₂ , _) ∈
          (Σ (id₁ a == inv₂ ◻ f) (λ eta₂ → eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta₂) ×
          (Σ (id₁ b == f ◻ inv₂) (λ eps₂ → eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps₂))) ] ×
            ((ρ f ∙ ap (λ m → f ◻ m) eta₂ ∙ α f inv₂ f == lamb f ∙ ap (λ m → m ◻ f) eps₂) ×
            (ρ inv₂ ∙ ap (λ m → inv₂ ◻ m) eps₂ ∙ α inv₂ f inv₂ == lamb inv₂ ∙ ap (λ m → m ◻ inv₂) eta₂))
    Adjeq≃-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = Σ (hom b a) (λ inv₂ → inv α₁ == inv₂)} pathfrom-is-contr-instance)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red (×-level pathfrom-is-contr-instance pathfrom-is-contr-instance))⁻¹)
          {{×-level (inhab-prop-is-contr (coher-map α₁)) (inhab-prop-is-contr (coher-inv α₁))}}}}

    abstract
      Adjeq≃-contr : is-contr (Σ (Adjequiv f) (λ α₂ → α₁ Adjeq≃ α₂))
      Adjeq≃-contr = equiv-preserves-level lemma {{Adjeq≃-contr-aux}}
        where
          lemma :
            [ (inv₂ , e-inv) ∈ Σ (hom b a) (λ inv₂ → inv α₁ == inv₂) ] ×
              [ ((eta₂ , _) , eps₂ , _) ∈
              (Σ (id₁ a == inv₂ ◻ f) (λ eta₂ → eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta₂) ×
              (Σ (id₁ b == f ◻ inv₂) (λ eps₂ → eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps₂))) ] ×
                ((ρ f ∙ ap (λ m → f ◻ m) eta₂ ∙ α f inv₂ f == lamb f ∙ ap (λ m → m ◻ f) eps₂) ×
                (ρ inv₂ ∙ ap (λ m → inv₂ ◻ m) eps₂ ∙ α inv₂ f inv₂ == lamb inv₂ ∙ ap (λ m → m ◻ inv₂) eta₂))
              ≃
            Σ (Adjequiv f) (λ α₂ → α₁ Adjeq≃ α₂)
          lemma =
            equiv
              (λ ((inv₂ , e-inv) , ((eta₂ , e-eta) , (eps₂ , e-eps)) , (cm₂ , ci₂)) → (Adj-eqv inv₂ eta₂ eps₂ cm₂ ci₂) , e-inv , (e-eta , e-eps))
              (λ ((Adj-eqv inv₂ eta₂ eps₂ cm₂ ci₂) , e-inv , (e-eta , e-eps)) → (inv₂ , e-inv) , ((eta₂ , e-eta) , (eps₂ , e-eps)) , (cm₂ , ci₂))
              (λ _ → idp)
              λ _ → idp

    Adjeq≃-ind : ∀ {k} (P : (α₂ : Adjequiv f) → (α₁ Adjeq≃ α₂ → Type k))
      → P α₁ (Adjeq≃-id α₁) → {α₂ : Adjequiv f} (e : α₁ Adjeq≃ α₂) → P α₂ e
    Adjeq≃-ind P = ID-ind-map P Adjeq≃-contr

    Adjeq≃-ind-β : ∀ {k} (P : (α₂ : Adjequiv f) → (α₁ Adjeq≃ α₂ → Type k))
      → (r : P α₁ (Adjeq≃-id α₁)) → Adjeq≃-ind P r (Adjeq≃-id α₁) == r
    Adjeq≃-ind-β P = ID-ind-map-β P Adjeq≃-contr

    Adjeq≃-to-== : {α₂ : Adjequiv f} → α₁ Adjeq≃ α₂ → α₁ == α₂ 
    Adjeq≃-to-== = Adjeq≃-ind (λ α₂ _ → α₁ == α₂) idp

  -- being an adjoint equivalence is a proposition

    Adjequiv-unique : {α₂ : Adjequiv f} → α₁ == α₂
    Adjequiv-unique {α₂} =  Adjeq≃-to-==
      (e-inv , coher , coher-r-to-coher-l {α₁} {α₂} e-inv coher)
      where

        e-inv : inv α₁ == inv α₂
        e-inv = <– (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) (! (eta α₁) ∙ eta α₂) 

        coher : eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂
        coher =
          ∙'=∙ (eta α₁) (ap (λ m → m ◻ f) e-inv) ∙
          ap (λ p → eta α₁ ∙ p) (<–-inv-r (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) (! (eta α₁) ∙ eta α₂)) ∙
          assoc-inv-l  (eta α₁) (eta α₂)  

  instance
    Adjequiv-is-prop : is-prop (Adjequiv f)
    Adjequiv-is-prop = all-paths-is-prop λ _ _ → Adjequiv-unique where open ae-SIP
-}
