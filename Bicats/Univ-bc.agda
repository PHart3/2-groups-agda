{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
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

is-univ-bc-≃ : ∀ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} → is-univ-bc ξB
  → {a b : B₀} → (a == b) ≃ (AdjEquiv ξB a b)
is-univ-bc-≃ {{ξB}} uB {a} {b} = ==-to-adjeq , uB a b

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} (uB : is-univ-bc ξB) {a : B₀} where

  abstract
    AdjEq-contr : is-contr (Σ B₀ (λ b → AdjEquiv ξB a b))
    AdjEq-contr = equiv-preserves-level (Σ-emap-r (λ b → is-univ-bc-≃ uB)) {{⟨⟩}}

  AdjEq-ind : ∀ {k} (P : (b : B₀) → (AdjEquiv ξB a b → Type k))
    → P a AdjEq-id₁ → {b : B₀} (e : AdjEquiv ξB a b) → P b e
  AdjEq-ind P = ID-ind-map P AdjEq-contr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {R : Psfunctor-nc {{ξB}} {{ξC}}} (uB : is-univ-bc ξB) where

  open Psfunctor-nc
  open PsfunctorNcStr

  abstract

    -- pseudofunctors preserve adjoint equivalences
    univ-pf-ae : {a b : B₀} ((f , _) : AdjEquiv ξB a b) → Adjequiv (F₁ (str-pf R) f)
    univ-pf-ae {a} = AdjEq-ind uB (λ _ (f , _) →  Adjequiv (F₁ (str-pf R) f))
      (transport Adjequiv (! (F-id₁ (str-pf R) a)) (snd AdjEq-id₁))

    -- the composite of adoint equivalences is an adjoint equivalence
    univ-ae-∘ : {b c : B₀} ((g , _) : AdjEquiv ξB b c) {a : B₀} ((f , _) : AdjEquiv ξB a b) → Adjequiv (⟦ ξB ⟧ g ◻ f)
    univ-ae-∘ {b} = AdjEq-ind uB (λ _ (g , _) → ∀ {a} ((f , _) : AdjEquiv ξB a b) → Adjequiv (⟦ ξB ⟧ g ◻ f))
      λ ae → transport Adjequiv (lamb (fst ae)) (snd ae)
