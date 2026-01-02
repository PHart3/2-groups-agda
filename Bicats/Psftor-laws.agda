
{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import Bicategory
open import Pstransf
open import Pstransf-SIP
open import Bicat-coher
open import Univ-bc

-- basic categorical laws for pseudofunctors

module Psftor-laws where

open BicatStr {{...}}
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} where

  -- associativity pseudotransformation
  module _ {i₃ i₄ j₃ j₄} {D₀ : Type i₃} {{ξD : BicatStr j₃ D₀}} {E₀ : Type i₄} {{ξE : BicatStr j₄ E₀}}
    (R₁ : Psfunctor-nc {{ξB}} {{ξC}}) (R₂ : Psfunctor-nc {{ξC}} {{ξD}}) (R₃ : Psfunctor-nc {{ξD}} {{ξE}}) where

    assoc-pst : Pstrans ((R₃ ∘BC-s R₂) ∘BC-s R₁) (R₃ ∘BC-s (R₂ ∘BC-s R₁))
    η₀ assoc-pst a = id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))
    η₁ assoc-pst f = 
      ! (ρ (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))) ∙
      lamb (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))
    coher-unit assoc-pst {a} = =ₛ-out $
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))
        (! (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a))) ∙
      lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a))) ◃∙
      ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))) ◻ m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∎
        =ₑ⟨ 2 & 1 &
          (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a))) ◃∙
          lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a)) ◃∎)  % =ₛ-in idp ⟩
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))
        (! (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      ! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a))) ◃∙
      lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))) ◻ m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∎
        =ₛ⟨ 3 & 2 & !ₛ (homotopy-naturality _ _ lamb
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
          ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
          F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a)))) ⟩
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))
        (! (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      ! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (id₁ a))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality-! ρ
          (! (ap (F₁ (str-pf R₃))
            (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
            F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ) ⟩
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∙
      ! (ρ (id₁ (map-pf R₃ ((map-pf R₂ ∘ map-pf R₁) a)))) ◃∙
      ap (λ m → m)
        (! (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ⟨ 0 & 2 & lamb-ρ-canc ⟩
      ap (λ m → m)
        (! (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ₁⟨ 0 & 1 & ap-! (λ m → m)
          (ap (F₁ (str-pf R₃))
            (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
          F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a)) ⟩
      ! (ap (λ m → m)
          (ap (F₁ (str-pf R₃))
            (ap (F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙ F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
          F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ₁⟨ 0 & 1 & ap ! (ap (ap (λ m → m))
          (ap-∘-∙-s  (F₁ (str-pf R₃)) (F₁ (str-pf R₂))
            (F-id₁ (str-pf R₁) a) (F-id₁ (str-pf R₂) (map-pf R₁ a)) (F-id₁ (str-pf R₃) ((map-pf R₂ ∘ map-pf R₁) a)))) ⟩
      ! (ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a)))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
        ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
        F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a))) ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ₁⟨ 0 & 2 & !-inv-l
          (ap (λ m → m)
            (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-id₁ (str-pf R₁) a) ∙
            ap (F₁ (str-pf R₃)) (F-id₁ (str-pf R₂) (map-pf R₁ a)) ∙
            F-id₁ (str-pf R₃) (map-pf R₂ (map-pf R₁ a)))) ⟩
      idp ◃∙
      lamb (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎
        =ₛ₁⟨ lamb-ρ-id₁-bc ⟩
      ρ (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a)))) ◃∎ ∎ₛ
    coher-assoc assoc-pst {a} {b} {c} f g = =ₛ-out $
      ! (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 0 & 1 & !-!-∙
          (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f)))
          (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f)) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality _ _ ρ
          (ap (F₁ (str-pf R₃))
            (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
            F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ρ (⟦ ξE ⟧ F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g) ◻ F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 4 & 1 & ap-!∙◃ (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
          (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f))
          (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ρ (⟦ ξE ⟧ F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g) ◻ F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ a))))) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
          (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f))) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 2 & 3 & trig-ρ-bc-rot-pre
          (F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g))
          (F₁ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f)) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (! (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ∙
        lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 4 & 1 & ap-!∙◃ (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
          (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g))
          (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ap (λ m → ⟦ ξE ⟧ (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g ◻ m)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      α
        ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)
        (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ b))))
        (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
          (ρ (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g))) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 2 & 3 & tri-bc◃-rot2-pre
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (ap (λ m → ⟦ ξE ⟧ id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))) ◻ m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∎
        =ₛ⟨ 4 & 1 & apCommSq◃! lamb
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ap (λ m → ⟦ ξE ⟧ m ◻  ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)
        (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (α
          (id₁ (map-pf R₃ (map-pf R₂ (map-pf R₁ c))))
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) g)
          (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) f)) ◃∙
      ! (lamb (⟦ ξE ⟧ F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)) ◻ F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)))) ◃∙
      ! (ap (λ m → m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∙
      lamb ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F₁ (str-pf R₁) (⟦ ξB ⟧ g ◻ f))) ◃∎
        =ₛ⟨ 2 & 3 & trig-lamb-bc-rot
          (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g))) (F₁ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃))
          (ap (F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙ F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g)) ◃∙
      ! (ap (λ m → m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∙
      lamb ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F₁ (str-pf R₁) (⟦ ξB ⟧ g ◻ f))) ◃∎
        =ₛ₁⟨ 1 & 1 & ap (ap (λ m → m)) (ap-∘-∙-s (F₁ (str-pf R₃)) (F₁ (str-pf R₂))
          (F-◻ (str-pf R₁) f g)
          (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g))
          (F-◻ (str-pf R₃) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) f) ((F₁ (str-pf R₂) ∘ F₁ (str-pf R₁)) g))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m)
        (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
        ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
        F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g))) ◃∙
      ! (ap (λ m → m)
          (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
          ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
          F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ◃∙
      lamb ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F₁ (str-pf R₁) (⟦ ξB ⟧ g ◻ f))) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-r
          (ap (λ m → m)
            (ap (F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F-◻ (str-pf R₁) f g) ∙
            ap (F₁ (str-pf R₃)) (F-◻ (str-pf R₂) (F₁ (str-pf R₁) f) (F₁ (str-pf R₁) g)) ∙
            F-◻ (str-pf R₃) (F₁ (str-pf R₂) (F₁ (str-pf R₁) f)) (F₁ (str-pf R₂) (F₁ (str-pf R₁) g)))) ⟩
      ! (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ◃∙
      idp ◃∙
      lamb ((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) (F₁ (str-pf R₁) (⟦ ξB ⟧ g ◻ f))) ◃∎
        =ₛ₁⟨ !-inv-l (lamb (((F₁ (str-pf R₃) ∘ F₁ (str-pf R₂)) ∘ F₁ (str-pf R₁)) (⟦ ξB ⟧ g ◻ f))) ⟩
      idp ◃∎ ∎ₛ

    assoc-psf-≃ : ((R₃ ∘BC-s R₂) ∘BC-s R₁) psf-≃ (R₃ ∘BC-s (R₂ ∘BC-s R₁))
    fst assoc-psf-≃ = assoc-pst
    snd assoc-psf-≃ _ = snd AdjEqv-id₁

    assoc-pst-nc : Pstrans-nc ((R₃ ∘BC-s R₂) ∘BC-s R₁) (R₃ ∘BC-s (R₂ ∘BC-s R₁))
    assoc-pst-nc = pstrans-str assoc-pst

  -- unit pseudotransformations
  module _ (R : Psfunctor-nc {{ξB}} {{ξC}}) where

    unitl-pst : Pstrans (idpfBC ∘BC-s R) R
    η₀ unitl-pst a = id₁ (map-pf R a)
    η₁ unitl-pst f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)
    coher-unit unitl-pst {a} = =ₛ-out $
      lamb (id₁ (map-pf R a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
      (! (ρ (F₁ (str-pf R) (id₁ a))) ∙
      lamb (F₁ (str-pf R) (id₁ a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)
        (ap (F₁ (str-pf idpfBC)) (F-id₁ (str-pf R) a) ∙ F-id₁ (str-pf idpfBC) (map-pf R a)) ◃∎
        =ₑ⟨ 2 & 1 &
          (! (ρ (F₁ (str-pf R) (id₁ a))) ◃∙
          lamb (F₁ (str-pf R) (id₁ a)) ◃∎)  % =ₛ-in idp ⟩
      lamb (id₁ (map-pf R a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ a))) ◃∙
      lamb (F₁ (str-pf R) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)
        (ap (F₁ (str-pf idpfBC)) (F-id₁ (str-pf R) a) ∙ F-id₁ (str-pf idpfBC) (map-pf R a)) ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a) ⟩
      lamb (id₁ (map-pf R a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ a))) ◃∙
      lamb (F₁ (str-pf R) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)
        (ap (F₁ (str-pf idpfBC)) (F-id₁ (str-pf R) a) ∙ F-id₁ (str-pf idpfBC) (map-pf R a)) ◃∎
        =ₛ₁⟨ 4 & 1 & ap (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)) (ap-idf-idp (F-id₁ (str-pf R) a)) ⟩
      lamb (id₁ (map-pf R a)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-id₁ (str-pf R) a)) ◃∙
      ! (ρ (F₁ (str-pf R) (id₁ a))) ◃∙
      lamb (F₁ (str-pf R) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
        =ₛ⟨ 1 & 2 & homotopy-naturality-!-! ρ (F-id₁ (str-pf R) a) ⟩
      lamb (id₁ (map-pf R a)) ◃∙
      ! (ρ (id₁ (map-pf R a))) ◃∙
      ! (ap (λ m → m) (F-id₁ (str-pf R) a)) ◃∙
      lamb (F₁ (str-pf R) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
        =ₛ⟨ 0 & 2 & lamb-ρ-canc ⟩
      ! (ap (λ m → m) (F-id₁ (str-pf R) a)) ◃∙
      lamb (F₁ (str-pf R) (id₁ a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
        =ₛ⟨ !ₛ (apCommSq2◃ lamb (F-id₁ (str-pf R) a)) ⟩
      lamb (id₁ (map-pf R a)) ◃∎
        =ₛ₁⟨ lamb-ρ-id₁-bc ⟩
      ρ (id₁ (map-pf R a)) ◃∎ ∎ₛ
    coher-assoc unitl-pst {a} {b} {c} f g = =ₛ-out $
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙
        lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m)
        (! (ρ (F₁ (str-pf R) f)) ∙
        lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
        (! (ρ (F₁ (str-pf R) g)) ∙
        lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 0 & 1 & !-!-∙
          (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)))
          (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m)
        (! (ρ (F₁ (str-pf R) f)) ∙
        lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
        (! (ρ (F₁ (str-pf R) g)) ∙
        lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality _ _ ρ (F-◻ (str-pf R) f g)) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m)
        (! (ρ (F₁ (str-pf R) f)) ∙
        lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
        (! (ρ (F₁ (str-pf R) g)) ∙
        lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 4 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m)
          (ρ (F₁ (str-pf R) f))
          (lamb (F₁ (str-pf R) f)) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ρ (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (ρ (F₁ (str-pf R) f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
        (! (ρ (F₁ (str-pf R) g)) ∙
        lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 2 & 3 & trig-ρ-bc-rot-pre (F₁ (str-pf R) g) (F₁ (str-pf R) f) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
        (! (ρ (F₁ (str-pf R) g)) ∙
        lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 4 & 1 & ap-!∙◃ (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f)
          (ρ (F₁ (str-pf R) g))
          (lamb (F₁ (str-pf R) g)) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (ρ (F₁ (str-pf R) g))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 2 & 3 & tri-bc◃-rot2-pre (F₁ (str-pf R) f) (F₁ (str-pf R) g) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 2 & 2 & trig-lamb-bc (F₁ (str-pf R) g) (F₁ (str-pf R) f) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      lamb (⟦ ξC ⟧ F₁ (str-pf R) g ◻ F₁ (str-pf R) f) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ⟨ 2 & 2 & homotopy-naturality-!ap lamb (ap (λ m → m) (F-◻ (str-pf R) f g) ∙ idp) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ! (ap (λ m → m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∙
      lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)) ◃∎
        =ₛ₁⟨ 2 & 1 & ap ! (ap (ap (λ m → m)) (ap-idf-idp (F-◻ (str-pf R) f g))) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → m) (F-◻ (str-pf R) f g) ◃∙
      ! (ap (λ m → m) (F-◻ (str-pf R) f g)) ◃∙
      lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-r (ap (λ m → m) (F-◻ (str-pf R) f g)) ⟩
      ! (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      idp ◃∙
      lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f)) ◃∎
        =ₛ₁⟨ !-inv-l (lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ⟩
      idp ◃∎ ∎ₛ

    unitl-psf-≃ : (idpfBC ∘BC-s R) psf-≃ R
    fst unitl-psf-≃ = unitl-pst
    snd unitl-psf-≃ _ = snd AdjEqv-id₁

    unitl-pst-nc : Pstrans-nc (idpfBC ∘BC-s R) R
    unitl-pst-nc = pstrans-str unitl-pst

    unitr-pst : Pstrans R (R ∘BC-s idpfBC)
    η₀ unitr-pst a = id₁ (map-pf R a)
    η₁ unitr-pst f = ! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)
    coher-unit unitr-pst {a} = =ₛ-out $
      lamb (id₁ (map-pf R a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
      (! (ρ (F₁ (str-pf R) (id₁ a))) ∙
      lamb (F₁ (str-pf R) (id₁ a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m) (F-id₁ (str-pf R) a) ◃∎
        =ₛ₁⟨ 3 & 1 & ! (ap (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)) (ap-idf-idp (F-id₁ (str-pf R) a))) ⟩
      lamb (id₁ (map-pf R a)) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (! (F-id₁ (str-pf R) a)) ◃∙
      (! (ρ (F₁ (str-pf R) (id₁ a))) ∙
      lamb (F₁ (str-pf R) (id₁ a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R a) ◻ m)
        (ap (F₁ (str-pf idpfBC)) (F-id₁ (str-pf R) a) ∙ F-id₁ (str-pf idpfBC) (map-pf R a)) ◃∎
        =ₛ₁⟨ coher-unit unitl-pst ⟩
      ρ (id₁ (map-pf R a)) ◃∎ ∎ₛ
    coher-assoc unitr-pst {a} {b} {c} f g = =ₛ-out $
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) (F₁ (str-pf (idpfBC {{ξB}})) f) (F₁ (str-pf (idpfBC {{ξB}})) g)) ◃∙
      ! (α ((F₁ (str-pf R) ∘ F₁ (str-pf (idpfBC {{ξB}}))) g) ((F₁ (str-pf R) ∘ F₁ (str-pf (idpfBC {{ξB}}))) f) (id₁ (map-pf R a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ (F₁ (str-pf R) ∘ F₁ (str-pf (idpfBC {{ξB}}))) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
      α ((F₁ (str-pf R) ∘ F₁ (str-pf (idpfBC {{ξB}}))) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m) (F-◻ (str-pf R) f g)) ◃∎
        =ₛ₁⟨ 7 & 1 & ! (ap ! (ap (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)) (ap-idf-idp (F-◻ (str-pf R) f g)))) ⟩
      ! (! (ρ (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ∙ lamb (F₁ (str-pf R) (⟦ ξB ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ id₁ (map-pf R a)) (F-◻ (str-pf R) f g) ◃∙
      ! (α (F₁ (str-pf R) g) (F₁ (str-pf R) f) (id₁ (map-pf R a))) ◃∙
      ap (λ m → ⟦ ξC ⟧ F₁ (str-pf R) g ◻ m) (! (ρ (F₁ (str-pf R) f)) ∙ lamb (F₁ (str-pf R) f)) ◃∙
      α (F₁ (str-pf R) g) (id₁ (map-pf R b)) (F₁ (str-pf R) f) ◃∙
      ap (λ m → ⟦ ξC ⟧ m ◻ F₁ (str-pf R) f) (! (ρ (F₁ (str-pf R) g)) ∙ lamb (F₁ (str-pf R) g)) ◃∙
      ! (α (id₁ (map-pf R c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ◃∙
      ! (ap (λ m → ⟦ ξC ⟧ id₁ (map-pf R c) ◻ m)
          (ap (F₁ (str-pf idpfBC)) (F-◻ (str-pf R) f g) ∙
          F-◻ (str-pf idpfBC) (F₁ (str-pf R) f) (F₁ (str-pf R) g))) ◃∎
        =ₛ₁⟨ coher-assoc unitl-pst f g ⟩
      idp ◃∎ ∎ₛ

    unitr-psf-≃ : R psf-≃ (R ∘BC-s idpfBC)
    fst unitr-psf-≃ = unitr-pst
    snd unitr-psf-≃ _ = snd AdjEqv-id₁

    unitr-pst-nc : Pstrans-nc R (R ∘BC-s idpfBC)
    unitr-pst-nc = pstrans-str unitr-pst
