{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import Bicategory
open import AdjEqv
open import Bicat-coher

module Univ-bc where

open BicatStr {{...}}

-- (globally) univalent bicategory

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} where

  open Adjequiv

  AdjEqv-id₁ : {a : B₀} → AdjEquiv ξB a a
  fst (AdjEqv-id₁ {a}) = id₁ a
  inv (snd (AdjEqv-id₁ {a})) = id₁ a
  eta (snd (AdjEqv-id₁ {a})) = lamb (id₁ a)
  eps (snd (AdjEqv-id₁ {a})) = lamb (id₁ a)
  coher-map (snd (AdjEqv-id₁ {a})) = =ₛ-out $
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
  coher-inv (snd (AdjEqv-id₁ {a})) = =ₛ-out $
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
  ==-to-adjeq idp = AdjEqv-id₁

is-univ-bc : ∀ {i j} {B₀ : Type i} → BicatStr j B₀ → Type (lmax i j)
is-univ-bc {B₀ = B₀} ξB = (a b : B₀) → is-equiv (==-to-adjeq {{ξB}} {a} {b})

is-univ-bc-inst : ∀ {i j} {B₀ : Type i} {{_ : BicatStr j B₀}} → Type (lmax i j)
is-univ-bc-inst {B₀ = B₀} {{ξB}} = {a b : B₀} → is-equiv (==-to-adjeq {{ξB}} {a} {b})

is-univ-bc-≃ : ∀ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} → is-univ-bc ξB
  → {a b : B₀} → (a == b) ≃ (AdjEquiv ξB a b)
is-univ-bc-≃ {{ξB}} uB {a} {b} = ==-to-adjeq , uB a b

ubc-ae-to-== : ∀ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} {{uB : is-univ-bc-inst {{ξB}}}}
  → {a b : B₀} → AdjEquiv ξB a b → a == b
ubc-ae-to-== {{uB = uB}} f = <– (is-univ-bc-≃ (λ _ _ → uB)) f

module _ {i j} {B₀ : Type i} {{ξB : BicatStr j B₀}} (uB : is-univ-bc ξB) {a : B₀} where

  abstract
    AdjEqv-contr : is-contr (Σ B₀ (λ b → AdjEquiv ξB a b))
    AdjEqv-contr = equiv-preserves-level (Σ-emap-r (λ b → is-univ-bc-≃ uB)) {{⟨⟩}}

  AdjEqv-ind : ∀ {k} (P : (b : B₀) → (AdjEquiv ξB a b → Type k))
    → P a AdjEqv-id₁ → {b : B₀} (e : AdjEquiv ξB a b) → P b e
  AdjEqv-ind P = ID-ind-map P AdjEqv-contr

module _ {i₁ j₁} {B₀ : Type i₁} {{ξB : BicatStr j₁ B₀}} (uB : is-univ-bc ξB) where

  open Psfunctor-nc
  open PsfunctorNcStr

  abstract

    -- pseudofunctors preserve adjoint equivalences
    univ-pf-ae : ∀ {i₂ j₂} {C₀ : Type i₂} {{ξC : BicatStr j₂ C₀}}
      {R : Psfunctor-nc {{ξB}} {{ξC}}} {a b : B₀} ((f , _) : AdjEquiv ξB a b) → Adjequiv {{ξC}} (F₁ (str-pf R) f)
    univ-pf-ae {R = R} {a} = AdjEqv-ind uB (λ _ (f , _) →  Adjequiv (F₁ (str-pf R) f))
      (transport Adjequiv (! (F-id₁ (str-pf R) a)) (snd AdjEqv-id₁))

    -- the composite of adoint equivalences is an adjoint equivalence
    univ-ae-∘ : {b c : B₀} ((g , _) : AdjEquiv ξB b c) {a : B₀} ((f , _) : AdjEquiv ξB a b) → Adjequiv (⟦ ξB ⟧ g ◻ f)
    univ-ae-∘ {b} = AdjEqv-ind uB (λ _ (g , _) → ∀ {a} ((f , _) : AdjEquiv ξB a b) → Adjequiv (⟦ ξB ⟧ g ◻ f))
      λ ae → transport Adjequiv (lamb (fst ae)) (snd ae)
