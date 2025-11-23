{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEq
open import Bicat-coher
open import Pstransf
open import Univ-bc

-- identity pseudotransformation

module Pstransf-id where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂}
  {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

    Pstrans-id : (R : Psfunctor {{ξB}} {{ξC}}) → Pstrans R R
    η₀ (Pstrans-id R) x = id₁ (map-pf R x)
    η₁ (Pstrans-id R) f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)
    coher-unit (Pstrans-id R) {x} = =ₛ-out $
      lamb (id₁ (map-pf R x)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (! (F-id₁ (str-pf R) x)) ◃∙
      (! (ρ (F₁ (str-pf R) (id₁ x))) ∙ lamb (F₁ (str-pf R) (id₁ x))) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R x) ◻ m) (F-id₁ (str-pf R) x) ◃∎
        =ₑ⟨ 2 & 1 & (! (ρ (F₁ (str-pf R) (id₁ x))) ◃∙ lamb (F₁ (str-pf R) (id₁ x)) ◃∎) % =ₛ-in idp ⟩
      lamb (id₁ (map-pf R x)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (! (F-id₁ (str-pf R) x)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ x))) ◃∙
      lamb (F₁ (str-pf R) (id₁ x)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R x) ◻ m) (F-id₁ (str-pf R) x) ◃∎
        =ₛ⟨ 3 & 2 & !ₛ (homotopy-naturality _ _ lamb (F-id₁ (str-pf R) x)) ⟩
      lamb (id₁ (map-pf R x)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (! (F-id₁ (str-pf R) x)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ x))) ◃∙
      ap (λ m → m) (F-id₁ (str-pf R) x) ◃∙
      lamb (id₁ (map-pf R x)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-id₁ (str-pf R) x) ⟩
      lamb (id₁ (map-pf R x)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-id₁ (str-pf R) x)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ x))) ◃∙
      ap (λ m → m) (F-id₁ (str-pf R) x) ◃∙
      lamb (id₁ (map-pf R x)) ◃∎
        =ₛ⟨ 1 & 3 & !ₛ (apCommSq2◃! ρ (F-id₁ (str-pf R) x)) ⟩
      lamb (id₁ (map-pf R x)) ◃∙
      ! (ρ (id₁ (map-pf R x))) ◃∙
      lamb (id₁ (map-pf R x)) ◃∎
        =ₛ₁⟨ 0 & 1 & lamb-ρ-id₁-bc ⟩
      ρ (id₁ (map-pf R x)) ◃∙
      ! (ρ (id₁ (map-pf R x))) ◃∙
      lamb (id₁ (map-pf R x)) ◃∎
        =ₛ₁⟨ 0 & 2 & !-inv-r (ρ (id₁ (map-pf R x))) ⟩
      idp ◃∙
      lamb (id₁ (map-pf R x)) ◃∎
        =ₛ₁⟨ lamb-ρ-id₁-bc ⟩
      ρ (id₁ (map-pf R x)) ◃∎ ∎ₛ 
    coher-assoc (Pstrans-id R) {x} {y} {z} f g = =ₛ-out $
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 5 & 1 &
          ap-!∙◃ (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g)) (lamb (F₁ (str-pf R) g)) ⟩
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 3 & 1 &
          ap-!∙◃ (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f)) (lamb (F₁ (str-pf R) f)) ⟩
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 0 & 1 & !-!-∙ (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R x)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality _ _ ρ (F-◻ (str-pf R) f g)) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 0 & 2 & homotopy-naturality-! lamb (F-◻ (str-pf R) f g) ⟩
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g) ◃∙
      ! (lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
      ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R x))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 2 & 3 & trig-ρ-bc-rot-pre (F₁ (str-pf R) g) (F₁ (str-pf R) f) ⟩
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g) ◃∙
      ! (lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R y)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 2 & 3 & tri-bc◃-rot2-pre (F₁ (str-pf R) f) (F₁ (str-pf R) g) ⟩
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g) ◃∙
      ! (lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R z)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ⟨ 1 & 3 & trig-lamb-bc-rot3 (F₁ (str-pf R) g) (F₁ (str-pf R) f) ⟩
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ₁⟨ !-inv-r (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R z) ◻ m) (F-◻ (str-pf R) f g)) ⟩
      idp ◃∎ ∎ₛ

    ps-≃-id : {R : Psfunctor {{ξB}} {{ξC}}} → R ps-≃ R
    fst (ps-≃-id {R}) = Pstrans-id R
    snd ps-≃-id _ = snd AdjEq-id₁
