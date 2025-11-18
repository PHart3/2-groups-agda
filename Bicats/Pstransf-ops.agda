{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import Bicategory
open import Bicat-coher
open import Pstransf

-- operations on pseudotransformations

module Pstransf-ops where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- composition

  infixr 70 _pstrans-∘_
  _pstrans-∘_ : {R₁ R₂ R₃ : Psfunctor {{ξB}} {{ξC}}} → Pstrans R₂ R₃ → Pstrans R₁ R₂ → Pstrans R₁ R₃
  η₀ (T₂ pstrans-∘ T₁) a = η₀ T₂ a ◻ η₀ T₁ a
  η₁ (_pstrans-∘_ {R₁} {R₂} {R₃} T₂ T₁) {x} {y} f = 
    -- ⟦ ξC ⟧ F₁ (str-pf R₃) f ◻ ⟦ ξC ⟧ η₀ T₂ x ◻ η₀ T₁ x
    α (F₁ (str-pf R₃) f) (η₀ T₂ x) (η₀ T₁ x) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ F₁ (str-pf R₃) f ◻  η₀ T₂ x) ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ x) (η₁ T₂ f) ∙
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ F₁ (str-pf R₂) f) ◻ η₀ T₁ x
    ! (α (η₀ T₂ y) (F₁ (str-pf R₂) f) (η₀ T₁ x)) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ F₁ (str-pf R₂) f ◻ η₀ T₁ x
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ y ◻ m) (η₁ T₁ f) ∙
    -- ⟦ ξC ⟧ η₀ T₂ y ◻ ⟦ ξC ⟧ η₀ T₁ y ◻ F₁ (str-pf R₁) f
    α (η₀ T₂ y) (η₀ T₁ y) (F₁ (str-pf R₁) f)
    -- ⟦ ξC ⟧ (⟦ ξC ⟧ η₀ T₂ y ◻ η₀ T₁ y) ◻ F₁ (str-pf R₁) f
  coher-unit (_pstrans-∘_ {R₁} {R₂} {R₃} T₂ T₁) {a} = =ₛ-out $
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (! (F-id₁ (str-pf R₃) a)) ◃∙
    (α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ (id₁ a)) ∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (η₁ T₁ (id₁ a)) ∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₑ⟨ 2 & 1 &
        (α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
        ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ (id₁ a)) ◃∙
        ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
        ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (η₁ T₁ (id₁ a)) ◃∙
        α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∎)
        % =ₛ-in idp ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (! (F-id₁ (str-pf R₃) a)) ◃∙
    α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ (id₁ a)) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (η₁ T₁ (id₁ a)) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 5 & 1 & ap-seq-=ₛ (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (coher-unit◃-rot T₁) ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (! (F-id₁ (str-pf R₃) a)) ◃∙
    α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ (id₁ a)) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (coher-unit◃-rot T₂) ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (! (F-id₁ (str-pf R₃) a)) ◃∙
    α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ap (λ m → m ◻ η₀ T₂ a) (F-id₁ (str-pf R₃) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (lamb (η₀ T₂ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (ap (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a))) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ₁⟨ 3 & 1 & ∘-ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (λ m → m ◻ η₀ T₂ a) (F-id₁ (str-pf R₃) a) ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (! (F-id₁ (str-pf R₃) a)) ◃∙
    α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ η₀ T₂ a ◻ η₀ T₁ a) (F-id₁ (str-pf R₃) a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (lamb (η₀ T₂ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (ap (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a))) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (F-id₁ (str-pf R₃) a) ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (F-id₁ (str-pf R₃) a)) ◃∙
    α (F₁ (str-pf R₃) (id₁ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ m ◻ η₀ T₂ a ◻ η₀ T₁ a) (F-id₁ (str-pf R₃) a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (lamb (η₀ T₂ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (ap (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a))) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 1 & 3 & !ₛ (apCommSq2◃ (λ m → α m (η₀ T₂ a) (η₀ T₁ a)) (F-id₁ (str-pf R₃) a)) ⟩
    lamb (η₀ T₂ a ◻ η₀ T₁ a) ◃∙
    α (id₁ (map-pf R₃ a)) (η₀ T₂ a) (η₀ T₁ a) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (lamb (η₀ T₂ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (ap (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a))) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 0 & 3 & !ₛ (trig-lamb-bc-rot2 (η₀ T₂ a) (η₀ T₁ a)) ⟩
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (! (ap (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a))) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ₁⟨ 1 & 1 & !-∘-ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (λ m → η₀ T₂ a ◻ m) (F-id₁ (str-pf R₂) a) ⟩
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ap (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ₁⟨ 3 & 1 & ∘-ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (λ m → m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a) ⟩
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a)) ◃∙
    ! (α (η₀ T₂ a) (F₁ (str-pf R₂) (id₁ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ ⟦ ξC ⟧ m ◻ η₀ T₁ a) (F-id₁ (str-pf R₂) a) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 1 & 3 & !ₛ (apCommSq2◃! (λ m → α (η₀ T₂ a) m (η₀ T₁ a)) (F-id₁ (str-pf R₂) a)) ⟩
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (ρ (η₀ T₂ a)) ◃∙
    ! (α (η₀ T₂ a) (id₁ (map-pf R₂ a)) (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (lamb (η₀ T₁ a))) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 0 & 3 & !ₛ (tri-bc◃-rot3 (η₀ T₁ a) (η₀ T₂ a)) ⟩
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (! (ap (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a))) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ₁⟨ 1 & 1 & !-∘-ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (λ m → η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ⟩
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ ⟦ ξC ⟧ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a)) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (F₁ (str-pf R₁) (id₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a ◻ m) (F-id₁ (str-pf R₁) a) ◃∎
      =ₛ⟨ 1 & 3 & !ₛ (apCommSq2◃ (α (η₀ T₂ a) (η₀ T₁ a)) (F-id₁ (str-pf R₁) a)) ⟩
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ a ◻ m) (ρ (η₀ T₁ a)) ◃∙
    α (η₀ T₂ a) (η₀ T₁ a) (id₁ (map-pf R₁ a)) ◃∎
      =ₛ⟨ trig-ρ-bc (η₀ T₂ a) (η₀ T₁ a) ⟩
    ρ (η₀ T₂ a ◻ η₀ T₁ a) ◃∎ ∎ₛ
  coher-assoc (_pstrans-∘_ {R₁} {R₂} {R₃} T₂ T₁) {a} {b} {c} f g = =ₛ-out $
    ! (α (F₁ (str-pf R₃) (⟦ ξB ⟧ g ◻ f)) (η₀ T₂ a) (η₀ T₁ a) ∙
    ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ (⟦ ξB ⟧ g ◻ f)) ∙
    ! (α (η₀ T₂ c) (F₁ (str-pf R₂) (⟦ ξB ⟧ g ◻ f)) (η₀ T₁ a)) ∙
    ap (λ m → ⟦ ξC ⟧ η₀ T₂ c ◻ m) (η₁ T₁ (⟦ ξB ⟧ g ◻ f)) ∙
    α (η₀ T₂ c) (η₀ T₁ c) (F₁ (str-pf R₁) (⟦ ξB ⟧ g ◻ f))) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ ⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a) (F-◻ (str-pf R₃) f g) ◃∙
    ! (α (F₁ (str-pf R₃) g) (F₁ (str-pf R₃) f) (⟦ ξC ⟧ η₀ T₂ a ◻ η₀ T₁ a)) ◃∙
    ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R₃) g ◻ m)
      (α (F₁ (str-pf R₃) f) (η₀ T₂ a) (η₀ T₁ a) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ a) (η₁ T₂ f) ∙
      ! (α (η₀ T₂ b) (F₁ (str-pf R₂) f) (η₀ T₁ a)) ∙
      ap (λ m → ⟦ ξC ⟧ η₀ T₂ b ◻ m) (η₁ T₁ f) ∙
      α (η₀ T₂ b) (η₀ T₁ b) (F₁ (str-pf R₁) f)) ◃∙
    α (F₁ (str-pf R₃) g) (⟦ ξC ⟧ η₀ T₂ b ◻ η₀ T₁ b) (F₁ (str-pf R₁) f) ◃∙
    ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R₁) f)
      (α (F₁ (str-pf R₃) g) (η₀ T₂ b) (η₀ T₁ b) ∙
      ap (λ m → ⟦ ξC ⟧ m ◻ η₀ T₁ b) (η₁ T₂ g) ∙
      ! (α (η₀ T₂ c) (F₁ (str-pf R₂) g) (η₀ T₁ b)) ∙
      ap (λ m → ⟦ ξC ⟧ η₀ T₂ c ◻ m) (η₁ T₁ g) ∙
      α (η₀ T₂ c) (η₀ T₁ c) (F₁ (str-pf R₁) g)) ◃∙
    ! (α (⟦ ξC ⟧ η₀ T₂ c ◻ η₀ T₁ c) (F₁ (str-pf R₁) g) (F₁ (str-pf R₁) f)) ◃∙
    ! (ap (λ m → ⟦ ξC ⟧ ⟦ ξC ⟧ η₀ T₂ c ◻ η₀ T₁ c ◻ m) (F-◻ (str-pf R₁) f g)) ◃∎
      =ₛ⟨ {!!} ⟩
    {!!}

  -- left whiskering

  -- right whiskering

  -- associativity pseudotransformation (and its inverse)

  -- unit pseudotransformations

  -- the triangle identities
