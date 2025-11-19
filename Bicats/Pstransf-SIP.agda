{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory
open import Pstransf

-- SIP for (non-coherent) pseudotransformations

module Pstransf-SIP where

open BicatStr {{...}}
open Psfunctor
open PsfunctorStr

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {R S : Psfunctor {{ξB}} {{ξC}}} where

  -- invertible modifications between pseudotransformations
  record Pst-≃ (T₁ T₂ : Pstrans-nc R S) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor pst-≃
    field
      η₀-∼ : (a : B₀) → η₀-nc T₁ a == η₀-nc T₂ a
      η₁-∼ : {a b : B₀} (f : hom a b) →
        ! (η₁-nc T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (η₀-∼ a) ∙ η₁-nc T₂ f ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (η₀-∼ b)) == idp

  open Pst-≃

  Pst-≃-id : (T : Pstrans-nc R S) → Pst-≃ T T
  η₀-∼ (Pst-≃-id T) _ = idp
  η₁-∼ (Pst-≃-id T) f = !-inv-l-unit-r (η₁-nc T f)

  module _ {T₁ : Pstrans-nc R S} where

    private
      tot-sp =
        [ η₀2 ∈ ((a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀-nc T₁ a == η₀2)) ] ×
          ((((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom a b)) →
            Σ (F₁ (str-pf S) f ◻ fst (η₀2 a) == ⟦ ξC ⟧ fst (η₀2 b) ◻ F₁ (str-pf R) f) (λ η₁2cmp →
              ! (η₁-nc T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (snd (η₀2 a)) ∙ η₁2cmp ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (snd (η₀2 b))) == idp))

    Pst-≃-contr-aux :
      is-contr tot-sp
    Pst-≃-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = (a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀-nc T₁ a == η₀2)} Π-level-instance)⁻¹)
        {{Π-level-instance {{λ {(_ , f)} → equiv-preserves-level (Σ-emap-r (λ η₁2cmp → !-∙-idp-idp-≃ (η₁-nc T₁ f) η₁2cmp))}}}}
    abstract
      Pst-≃-contr : is-contr (Σ (Pstrans-nc R S) (λ T₂ → Pst-≃ T₁ T₂))
      Pst-≃-contr = equiv-preserves-level lemma {{Pst-≃-contr-aux}}
        where
          lemma : tot-sp ≃ Σ (Pstrans-nc R S) (λ T₂ → Pst-≃ T₁ T₂)
          lemma =
            equiv
              (λ (η₀2 , η₁2) →
                pstrans-nc (fst ∘ η₀2) (λ f → fst (η₁2 (_ , f))) ,
                pst-≃ (snd ∘ η₀2) (λ f → snd (η₁2 (_ , f))))
              (λ (pstrans-nc η₀2 η₁2 , pst-≃ η₀-∼ η₁-∼) →
                (λ a → η₀2 a , η₀-∼ a) , (λ (_ , f) → (η₁2 f) , (η₁-∼ f)))
              (λ _ → idp)
              λ _ → idp

    Pst-≃-ind : ∀ {k} (P : (T₂ : Pstrans-nc R S) → (Pst-≃ T₁ T₂ → Type k))
      → P T₁ (Pst-≃-id T₁) → {T₂ : Pstrans-nc R S} (e : Pst-≃ T₁ T₂) → P T₂ e
    Pst-≃-ind P = ID-ind-map P Pst-≃-contr

    Pst-≃-ind-β : ∀ {k} (P : (T₂ : Pstrans-nc R S) → (Pst-≃ T₁ T₂ → Type k))
      → (r : P T₁ (Pst-≃-id T₁)) → Pst-≃-ind P r (Pst-≃-id T₁) == r
    Pst-≃-ind-β P = ID-ind-map-β P Pst-≃-contr

    abstract
      Pst-≃-to-== : {T₂ : Pstrans-nc R S} → Pst-≃ T₁ T₂ → T₁ == T₂ 
      Pst-≃-to-== = Pst-≃-ind (λ T₂ _ → T₁ == T₂) idp
