{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import lib.NType2
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory
open import Pstransf

-- SIP for (non-coherent) pseudotransformations

module Pstransf-SIP where

open BicatStr {{...}}
open Psfunctor-nc
open PsfunctorNcStr
open Pstrans-nc

module _ {i₁ i₂ j₁ j₂} {B₀ : Type i₁} {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
  {R S : Psfunctor-nc {{ξB}} {{ξC}}} where

  -- invertible modifications between pseudotransformations
  record InvMod (T₁ T₂ : Pstrans-nc R S) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor pst-≃
    field
      η₀-∼ : (a : B₀) → η₀ T₁ a == η₀ T₂ a
      η₁-∼ : {a b : B₀} (f : hom a b) →
        ! (η₁ T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (η₀-∼ a) ∙ η₁ T₂ f ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (η₀-∼ b)) == idp

  infix 8 InvMod
  syntax InvMod T₁ T₂ = T₁ ⇔ T₂

  open InvMod

  InvMod-id : {T : Pstrans-nc R S} → InvMod T T
  η₀-∼ (InvMod-id {T}) _ = idp
  η₁-∼ (InvMod-id {T}) f = !-inv-l-unit-r (η₁ T f)

  module _ {T₁ : Pstrans-nc R S} where

    private
      tot-sp =
        [ η₀2 ∈ ((a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀ T₁ a == η₀2)) ] ×
          ((((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom a b)) →
            Σ (F₁ (str-pf S) f ◻ fst (η₀2 a) == ⟦ ξC ⟧ fst (η₀2 b) ◻ F₁ (str-pf R) f) (λ η₁2cmp →
              ! (η₁ T₁ f) ∙ ap (λ m → F₁ (str-pf S) f ◻ m) (snd (η₀2 a)) ∙ η₁2cmp ∙ ! (ap (λ m → m ◻ F₁ (str-pf R) f) (snd (η₀2 b))) == idp))

    InvMod-contr-aux :
      is-contr tot-sp
    InvMod-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = (a : B₀) → Σ (hom (map-pf R a) (map-pf S a)) (λ η₀2 → η₀ T₁ a == η₀2)} Π-level-instance)⁻¹)
        {{Π-level-instance {{λ {(_ , f)} → equiv-preserves-level (Σ-emap-r (λ η₁2cmp → !-∙-idp-idp-≃ (η₁ T₁ f) η₁2cmp))}}}}
        
    abstract
      InvMod-contr : is-contr (Σ (Pstrans-nc R S) (λ T₂ → InvMod T₁ T₂))
      InvMod-contr = equiv-preserves-level lemma {{InvMod-contr-aux}}
        where
          lemma : tot-sp ≃ Σ (Pstrans-nc R S) (λ T₂ → InvMod T₁ T₂)
          lemma =
            equiv
              (λ (η₀2 , η₁2) →
                pstransnc (fst ∘ η₀2) (λ f → fst (η₁2 (_ , f))) ,
                pst-≃ (snd ∘ η₀2) (λ f → snd (η₁2 (_ , f))))
              (λ (pstransnc η₀2 η₁2 , pst-≃ η₀-∼ η₁-∼) →
                (λ a → η₀2 a , η₀-∼ a) , (λ (_ , f) → (η₁2 f) , (η₁-∼ f)))
              (λ _ → idp)
              λ _ → idp

    InvMod-ind : ∀ {k} (P : (T₂ : Pstrans-nc R S) → (InvMod T₁ T₂ → Type k))
      → P T₁ InvMod-id → {T₂ : Pstrans-nc R S} (e : InvMod T₁ T₂) → P T₂ e
    InvMod-ind P = ID-ind-map P InvMod-contr

    InvMod-ind-β : ∀ {k} (P : (T₂ : Pstrans-nc R S) → (InvMod T₁ T₂ → Type k))
      → (r : P T₁ InvMod-id) → InvMod-ind P r InvMod-id == r
    InvMod-ind-β P = ID-ind-map-β P InvMod-contr

    InvMod-to-== : {T₂ : Pstrans-nc R S} → InvMod T₁ T₂ → T₁ == T₂
    InvMod-to-== {T₂} = InvMod-ind (λ T₂ _ → T₁ == T₂) idp

    InvMod-to-==-β : InvMod-to-== InvMod-id == idp
    InvMod-to-==-β = InvMod-ind-β (λ T₂ _ → T₁ == T₂) idp

    InvMod-from-== : {T₂ : Pstrans-nc R S} → T₁ == T₂ → InvMod T₁ T₂
    InvMod-from-== idp = InvMod-id

  InvMod-==-≃ : {T₁ T₂ : Pstrans-nc R S} → (T₁ == T₂) ≃ (InvMod T₁ T₂)
  InvMod-==-≃ {T₁} = equiv InvMod-from-== InvMod-to-== aux1 aux2
    where
      aux1 : ∀ {T₂} (p : InvMod T₁ T₂) → InvMod-from-== (InvMod-to-== p) == p
      aux1 = InvMod-ind (λ _ p → InvMod-from-== (InvMod-to-== p) == p) (ap InvMod-from-== InvMod-to-==-β)

      aux2 : ∀ {T₂} (p : T₁ == T₂) → InvMod-to-== (InvMod-from-== p) == p
      aux2 idp = InvMod-to-==-β

  InvModc-==-≃ : {T₁ T₂ : Pstrans R S} → (T₁ == T₂) ≃ (InvMod (pstrans-str T₁) (pstrans-str T₂))
  InvModc-==-≃ =
    InvMod-==-≃ ∘e
    (Subtype=-econv (subtypeprop Pst-coh-data {{λ {ψ} → Pst-coh-data-is-prop {ψ = ψ}}}) _ _)⁻¹ ∘e
    ap-equiv Pstrans-Σ-≃  _ _

  open Pstrans

  abstract
    Pstrans-coh-induce : (T₁ : Pstrans R S) {T₂ : Pstrans-nc R S} → InvMod (pstrans-str T₁) T₂ → Pst-coh-data T₂
    Pstrans-coh-induce T₁ = InvMod-ind (λ T₂ _ → Pst-coh-data T₂) (coher-unit T₁ , coher-assoc T₁) 
