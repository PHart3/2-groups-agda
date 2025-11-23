{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEq
open import Bicat-coher

module Univ-bc where

open BicatStr {{...}}

-- (globally) univalent bicategory

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} where

  open Adjequiv

  AdjEq-id₁ : {a : B₀} → AdjEquiv ξB a a
  fst (AdjEq-id₁ {a}) = id₁ a
  inv (snd (AdjEq-id₁ {a})) = id₁ a
  eta (snd (AdjEq-id₁ {a})) = lamb (id₁ a)
  eps (snd (AdjEq-id₁ {a})) = lamb (id₁ a)
  coher-map (snd (AdjEq-id₁ {a})) = =ₛ-out $
    ρ (id₁ a) ◃∙
    ap (λ m → id₁ a ◻ m) (lamb (id₁ a)) ◃∙
    α (id₁ a) (id₁ a) (id₁ a) ◃∎
      =ₛ⟨ 2 & 1 & =ₛ-in (tri-bc (id₁ a) (id₁ a)) ⟩
    ρ (id₁ a) ◃∙
    ap (λ m → id₁ a ◻ m) (lamb (id₁ a)) ◃∙
    ! (ap (λ m → id₁ a ◻ m) (lamb (id₁ a))) ◃∙
    ap (λ m → m ◻ id₁ a) (ρ (id₁ a)) ◃∎
      =ₛ₁⟨ 1 & 2 & !-inv-r (ap (λ m → id₁ a ◻ m) (lamb (id₁ a))) ⟩
    ρ (id₁ a) ◃∙
    idp ◃∙
    ap (λ m → m ◻ id₁ a) (ρ (id₁ a)) ◃∎
      =ₛ⟨ =ₛ-in (ap (λ p → p ∙ ap (λ m → m ◻ id₁ a) p) (! lamb-ρ-id₁-bc)) ⟩
    lamb (id₁ a) ◃∙
    ap (λ m → m ◻ id₁ a) (lamb (id₁ a)) ◃∎ ∎ₛ
  coher-inv (snd (AdjEq-id₁ {a})) = =ₛ-out $
    ρ (id₁ a) ◃∙
    ap (λ m → id₁ a ◻ m) (lamb (id₁ a)) ◃∙
    α (id₁ a) (id₁ a) (id₁ a) ◃∎
      =ₛ⟨ 2 & 1 & =ₛ-in (tri-bc (id₁ a) (id₁ a)) ⟩
    ρ (id₁ a) ◃∙
    ap (λ m → id₁ a ◻ m) (lamb (id₁ a)) ◃∙
    ! (ap (λ m → id₁ a ◻ m) (lamb (id₁ a))) ◃∙
    ap (λ m → m ◻ id₁ a) (ρ (id₁ a)) ◃∎
      =ₛ₁⟨ 1 & 2 & !-inv-r (ap (λ m → id₁ a ◻ m) (lamb (id₁ a))) ⟩
    ρ (id₁ a) ◃∙
    idp ◃∙
    ap (λ m → m ◻ id₁ a) (ρ (id₁ a)) ◃∎
      =ₛ⟨ =ₛ-in (ap (λ p → p ∙ ap (λ m → m ◻ id₁ a) p) (! lamb-ρ-id₁-bc)) ⟩
    lamb (id₁ a) ◃∙
    ap (λ m → m ◻ id₁ a) (lamb (id₁ a)) ◃∎ ∎ₛ

  ==-to-adjeq : {a b : B₀} → a == b → AdjEquiv ξB a b
  ==-to-adjeq idp = AdjEq-id₁

is-univ-bc : ∀ {i j} {B₀ : Type i} → BicatStr j B₀ → Type (lmax i j)
is-univ-bc {B₀ = B₀} ξB = (a b : B₀) → is-equiv (==-to-adjeq {{ξB}} {a} {b})

is-univ-bc-≃ : ∀ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} → is-univ-bc ξB → {a b : B₀}
  → (a == b) ≃ (AdjEquiv ξB a b)
is-univ-bc-≃ {{ξB}} uB {a} {b} = ==-to-adjeq , uB a b
