{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory
open import Pstransf

-- SIP for pseudotransformations

module Pstransf-SIP where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {R S : Psfunctor {{ξB}} {{ξC}}} where

  -- invertible modifications between pseudotransformations
  record Pst-≃ (T₁ T₂ : Pstrans R S) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor pst-≃
    field
      η₀-∼ : (a : B₀) → η₀ T₁ a == η₀ T₂ a
      η₁-∼ : {a b : B₀} (f : hom a b) →
        ! (η₁ T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (η₀-∼ a) ∙ η₁ T₂ f ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (η₀-∼ b)) == idp

  open Pst-≃

  Pst-≃-id : (T : Pstrans R S) → Pst-≃ T T
  η₀-∼ (Pst-≃-id T) _ = idp
  η₁-∼ (Pst-≃-id T) f = !-inv-l-unit-r (η₁ T f)

  module _ {T₁ : Pstrans R S} where

    private
      tot-sp =
        [ η₀2 ∈ ((a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀ T₁ a == η₀2)) ] ×
          [ η₁2 ∈
            ((((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom a b)) →
              Σ (F₁ (str-pf S) f ◻ fst (η₀2 a) == ⟦ ξC ⟧ fst (η₀2 b) ◻ F₁ (str-pf R) f) (λ η₁2cmp →
                ! (η₁ T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (snd (η₀2 a)) ∙ η₁2cmp ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (snd (η₀2 b))) == idp)) ] ×
            (((a : B₀) →
              lamb (fst (η₀2 a)) ∙
              ap (λ m → m ◻ fst (η₀2 a)) (! (F-id₁ (str-pf S) a)) ∙
              fst (η₁2 (_ , id₁ a)) ∙
              ap (λ m → fst (η₀2 a) ◻ m) (F-id₁ (str-pf R) a)
                ==
              ρ (fst (η₀2 a))) ×
            ((((a , b , c) , f , g) : Σ (B₀ × B₀ × B₀) (λ (a , b , c) → hom a b × hom b c)) →
              ! (fst (η₁2 (_ , (⟦ ξB ⟧ g ◻ f)))) ∙
              ap (λ m → m ◻ fst (η₀2 a)) (F-◻ (str-pf S) f g) ∙
              ! (α (F₁ (str-pf S) g) (F₁ (str-pf S) f) (fst (η₀2 a))) ∙
              ap (λ m → F₁ (str-pf S) g ◻ m) (fst (η₁2 (_ , f))) ∙
              α (F₁ (str-pf S) g) (fst (η₀2 b)) (F₁ (str-pf R) f) ∙
              ap (λ m → m ◻ (F₁ (str-pf R) f)) (fst (η₁2 (_ , g))) ∙
              ! (α (fst (η₀2 c)) (F₁ (str-pf R) g) (F₁ (str-pf R) f)) ∙
              ! (ap (λ m → fst (η₀2 c) ◻ m) (F-◻ (str-pf R) f g))
                ==
              idp))

    Pst-≃-contr-aux :
      is-contr tot-sp
    Pst-≃-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = (a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀ T₁ a == η₀2)} Π-level-instance)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red (Π-level-instance {{λ {(_ , f)} →
            equiv-preserves-level (Σ-emap-r (λ η₁2cmp → !-∙-idp-idp-≃ (η₁ T₁ f) η₁2cmp))}}))⁻¹)
          {{×-level (inhab-prop-is-contr (λ _ → coher-unit T₁)) (inhab-prop-is-contr (λ (_ , f , g) → coher-assoc T₁ f g))}}}}
    abstract
      Pst-≃-contr : is-contr (Σ (Pstrans R S) (λ T₂ → Pst-≃ T₁ T₂))
      Pst-≃-contr = equiv-preserves-level lemma {{Pst-≃-contr-aux}}
        where
          lemma : tot-sp ≃ Σ (Pstrans R S) (λ T₂ → Pst-≃ T₁ T₂)
          lemma =
            equiv
              (λ (η₀2 , η₁2 , unit2 , coher2) →
                pstrans (fst ∘ η₀2) (λ f → fst (η₁2 (_ , f))) (λ {a} → unit2 a) (λ f g → coher2 (_ , f , g)) ,
                pst-≃ (snd ∘ η₀2) (λ f → snd (η₁2 (_ , f))))
              (λ (pstrans η₀2 η₁2 unit2 coher2 , pst-≃ η₀-∼ η₁-∼) →
                (λ a → η₀2 a , η₀-∼ a) , (λ (_ , f) → (η₁2 f) , (η₁-∼ f)) , ((λ a → unit2 {a}) , (λ (_ , f , g) → coher2 f g)))
              (λ _ → idp)
              λ _ → idp

    Pst-≃-ind : ∀ {k} (P : (T₂ : Pstrans R S) → (Pst-≃ T₁ T₂ → Type k))
      → P T₁ (Pst-≃-id T₁) → {T₂ : Pstrans R S} (e : Pst-≃ T₁ T₂) → P T₂ e
    Pst-≃-ind P = ID-ind-map P Pst-≃-contr

    Pst-≃-ind-β : ∀ {k} (P : (T₂ : Pstrans R S) → (Pst-≃ T₁ T₂ → Type k))
      → (r : P T₁ (Pst-≃-id T₁)) → Pst-≃-ind P r (Pst-≃-id T₁) == r
    Pst-≃-ind-β P = ID-ind-map-β P Pst-≃-contr

    abstract
      Pst-≃-to-== : {T₂ : Pstrans R S} → Pst-≃ T₁ T₂ → T₁ == T₂ 
      Pst-≃-to-== = Pst-≃-ind (λ T₂ _ → T₁ == T₂) idp
