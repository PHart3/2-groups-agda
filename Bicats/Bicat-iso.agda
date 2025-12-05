{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.FTID
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory
open import Bicat-iso-aux

-- isomorphism of (2,1)-categories and associated SIP

module Bicat-iso where

open BicatStr
open Psfunctor
open PsfunctorStr {{...}}

module _ {i₁ i₂ j₁ j₂ : ULevel} {B₀ : Type i₁} where

  is-iso-bc :  {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}}
    → Psfunctor {{ξB}} {{ξC}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-iso-bc φ = is-equiv (map-pf φ) × ((a b : B₀) → is-equiv (F₁ {a = a} {b}))

  iso-bc-is-prop :  {C₀ : Type i₂} {{ξB : BicatStr j₁ B₀}} {{ξC : BicatStr j₂ C₀}} {φ : Psfunctor {{ξB}} {{ξC}}} → is-prop (is-iso-bc φ)
  iso-bc-is-prop = ×-level ⟨⟩ Π-level-instance

  infixr 70 _iso-bc_
  _iso-bc_ : {C₀ : Type i₂}
    → BicatStr j₁ B₀ → BicatStr j₂ C₀ → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  ξB iso-bc ξC = Σ (Psfunctor {{ξB}} {{ξC}}) (λ φ → is-iso-bc {{ξB}} {{ξC}} φ)

module _ {i j} {B₀ : Type i} (ξB : BicatStr j B₀) where

  iso-bc-id : ξB iso-bc ξB
  fst iso-bc-id = idfBC {{ξB}}
  snd iso-bc-id = idf-is-equiv B₀ , λ a b → idf-is-equiv (hom ξB a b)

  abstract
    bc-contr : is-contr (Σ (Bicat j i) (λ (_ , ξC) → ξB iso-bc ξC))
    bc-contr = equiv-preserves-level lemma {{bc-contr-aux ξB}}
      where
        lemma : tot-iso-bc ξB ≃ Σ (Bicat j i) (λ (_ , ξC) → ξB iso-bc ξC)
        lemma =
          equiv
            (λ ((C₀ , F₀ , e₀) , (homC , F₁) , (id₁C , F-id) , (◻-C , F-◻) ,
              (ρC , F-ρ) , (lambC , F-λ) , (αC , F-α) , triC , pentC , truncC) →
                (C₀ ,
                bicatstr (curry homC) id₁C (λ g f → ◻-C (_ , (g , f)))
                  (λ f → ρC (_ , f)) (λ f → lambC (_ , f)) (λ h g f → αC (_ , (h , g , f)))
                  (λ f g → triC (_ , (f , g))) (λ f g h i → pentC (_ , (f , g , h , i))) {{truncC}}) ,
                (psfunctor F₀
                  {{psfunctorstr (λ {a} {b} f → –> (F₁ (a , b)) f) F-id (λ f g → F-◻ (_ , (g , f)))
                    (λ f → F-ρ (_ , f)) (λ f → F-λ (_ , f)) λ h g f → F-α (_ , (h , g , f))}}) ,
                (e₀ , λ a b → snd (F₁ (a , b))))
            (λ ((C₀ , ξC) , psfunctor F₀ {{σ}} , e₀ , e₁) →
              (C₀ , (F₀ , e₀)) ,
                (((λ (a , b) → hom ξC a b) , λ (a , b) → (F₁ {{ξB}} {{ξC}}) , (e₁ a b)) ,
                  ((id₁ ξC , F-id₁ {{ξB}} {{ξC}}) ,
                    (((λ (_ , (g , f)) → ⟦ ξC ⟧ g ◻ f) , λ (_ , (g , f)) → F-◻ {{ξB}} {{ξC}} f g) ,
                      (((λ (_ , f) → ρ ξC f) , λ (_ , f) → F-ρ {{ξB}} {{ξC}} f) ,
                        (((λ (_ , f) → lamb ξC f) , λ (_ , f) → F-λ {{ξB}} {{ξC}} f) ,
                          (((λ (_ , (h , g , f)) → α ξC h g f) , λ (_ , (h , g , f)) → F-α {{ξB}} {{ξC}} h g f) ,
                            (λ (_ , (f , g)) → tri-bc ξC f g) , ((λ (_ , (f , g , h , i)) → pent-bc ξC f g h i) ,
                            hom-trunc ξC))))))))
            (λ _ → idp)
            (λ _ → idp)

  bc-ind : ∀ {k} (P : ((_ , ξC)  : Bicat j i) → (ξB iso-bc ξC → Type k))
    → P _ iso-bc-id → {C@(_ , ξC) : Bicat j i} (p : ξB iso-bc ξC) → P C p
  bc-ind P = ID-ind-map P bc-contr

  bc-ind-β : ∀ {k} (P : ((_ , ξC) : Bicat j i) → (ξB iso-bc ξC → Type k))
    → (r : P _ iso-bc-id) → bc-ind P r iso-bc-id == r
  bc-ind-β P = ID-ind-map-β P bc-contr

module _ {i j : ULevel} where

  iso-bc-to-== : {B@(_ , ξB) C@(_ , ξC) : Bicat j i} → ξB iso-bc ξC → B == C
  iso-bc-to-== {B@(_ , ξB)} = bc-ind ξB (λ C _ → B == C) idp

  iso-bc-to-==-β : {(_ , ξB) : Bicat j i} → iso-bc-to-== (iso-bc-id ξB) == idp
  iso-bc-to-==-β {B@(_ , ξB)} = bc-ind-β ξB (λ C _ → B == C) idp

  iso-bc-from-== : {B@(_ , ξB) C : Bicat j i} → B == C → ξB iso-bc (snd C)
  iso-bc-from-== {(_ , ξB)} idp = iso-bc-id ξB

  iso-bc-==-≃ : {B@(_ , ξB) C@(_ , ξC) : Bicat j i} → (ξB iso-bc ξC) ≃ (B == C)
  iso-bc-==-≃ {B@(_ , ξB)} {C@(_ , ξC)} = equiv iso-bc-to-== iso-bc-from-== aux1 aux2
    where

      aux1 : ∀ {D} (p : B == D) → iso-bc-to-== (iso-bc-from-== p) == p
      aux1 idp = iso-bc-to-==-β

      aux2 : ∀ {D@(_ , ξD) : Bicat j i} (p : ξB iso-bc ξD) → iso-bc-from-== (iso-bc-to-== p) == p
      aux2 = bc-ind ξB (λ _ p → iso-bc-from-== (iso-bc-to-== p) == p) (ap iso-bc-from-== iso-bc-to-==-β)
