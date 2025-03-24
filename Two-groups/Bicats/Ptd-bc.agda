{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import lib.types.PtdFibration
open import Bicategory

-- the bicategory of pointed connected 2-types

module Ptd-bc where

Ptd02 : (i : ULevel) → Type (lsucc i)
Ptd02 i = Σ (Ptd i) (λ X → is-connected 0 (de⊙ X) × has-level 2 (de⊙ X))

module _ {i : ULevel} where

  open BicatStr

  Ptd02-bicat : BicatStr i (Ptd02 i)
  hom Ptd02-bicat (X , _) (Y , _) = X ⊙→ Y
  id₁ Ptd02-bicat (X , _) = ⊙idf X
  _◻_ Ptd02-bicat g f = g ⊙∘ f
  ρ Ptd02-bicat f = ⊙-comp-to-== (⊙∘-runit f)
  lamb Ptd02-bicat f = ⊙-comp-to-== (⊙∘-lunit f)
  α Ptd02-bicat h g f = ⊙-comp-to-== (⊙∘-α-comp h g f)
  tri-bc Ptd02-bicat {b = (Y , _)} f@(_ , idp) g@(_ , idp) = =ₛ-out $
    ⊙-comp-to-== (⊙∘-α-comp g (⊙idf Y) f) ◃∎
      =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== ((λ _ → idp) , idp)) ⟩
    ⊙-comp-to-== (!-⊙∼ (⊙∘-post g (⊙∘-lunit f)) ∙⊙∼ ⊙∘-pre f (⊙∘-runit g)) ◃∎
      =ₛ⟨ ⊙∘-conv (!-⊙∼ (⊙∘-post g (⊙∘-lunit f))) (⊙∘-pre f (⊙∘-runit g)) ⟩
    ⊙-comp-to-== (!-⊙∼ (⊙∘-post g (⊙∘-lunit f))) ◃∙
    ⊙-comp-to-== (⊙∘-pre f (⊙∘-runit g)) ◃∎
      =ₛ₁⟨ 1 & 1 & whisk⊙-conv-r (⊙∘-runit g) ⟩
    ⊙-comp-to-== (!-⊙∼ (⊙∘-post g (⊙∘-lunit f))) ◃∙
    ap (λ m → m ⊙∘ f) (⊙-comp-to-== (⊙∘-runit g)) ◃∎
      =ₛ₁⟨ 0 & 1 & !⊙-conv (⊙∘-post g (⊙∘-lunit f)) ⟩
    ! (⊙-comp-to-== (⊙∘-post g (⊙∘-lunit f))) ◃∙
    ap (λ m → m ⊙∘ f) (⊙-comp-to-== (⊙∘-runit g)) ◃∎
      =ₛ₁⟨ 0 & 1 & ap ! (whisk⊙-conv-l (⊙∘-lunit f)) ⟩
    ! (ap (λ m → g ⊙∘ m) (⊙-comp-to-== (⊙∘-lunit f))) ◃∙
    ap (λ m → m ⊙∘ f) (⊙-comp-to-== (⊙∘-runit g)) ◃∎ ∎ₛ
  pent-bc Ptd02-bicat f@(_ , idp) g@(_ , idp) h@(_ , idp) k@(_ , idp) = =ₛ-out $
    ⊙-comp-to-== (⊙∘-α-comp k h (g ⊙∘ f)) ◃∙
    ⊙-comp-to-== (⊙∘-α-comp (k ⊙∘ h) g f) ◃∎
      =ₛ⟨ !ₛ (⊙∘-conv (⊙∘-α-comp k h (g ⊙∘ f)) (⊙∘-α-comp (k ⊙∘ h) g f)) ⟩
    ⊙-comp-to-== (⊙∘-α-comp k h (g ⊙∘ f) ∙⊙∼ ⊙∘-α-comp (k ⊙∘ h) g f) ◃∎
      =ₛ₁⟨ ap ⊙-comp-to-== (⊙→∼-to-== ((λ _ → idp) , idp)) ⟩
    ⊙-comp-to-== (⊙∘-post k (⊙∘-α-comp h g f) ∙⊙∼ ⊙∘-α-comp k (h ⊙∘ g) f ∙⊙∼ ⊙∘-pre f (⊙∘-α-comp k h g)) ◃∎
      =ₛ⟨ ⊙∘-conv-tri (⊙∘-post k (⊙∘-α-comp h g f)) (⊙∘-α-comp k (h ⊙∘ g) f) (⊙∘-pre f (⊙∘-α-comp k h g)) ⟩
    ⊙-comp-to-== (⊙∘-post k (⊙∘-α-comp h g f)) ◃∙
    ⊙-comp-to-== (⊙∘-α-comp k (h ⊙∘ g) f) ◃∙
    ⊙-comp-to-== (⊙∘-pre f (⊙∘-α-comp k h g)) ◃∎
      =ₛ₁⟨ 0 & 1 & whisk⊙-conv-l (⊙∘-α-comp h g f) ⟩
    ap (λ m → k ⊙∘ m) (⊙-comp-to-== (⊙∘-α-comp h g f)) ◃∙
    ⊙-comp-to-== (⊙∘-α-comp k (h ⊙∘ g) f) ◃∙
    ⊙-comp-to-== (⊙∘-pre f (⊙∘-α-comp k h g)) ◃∎
      =ₛ₁⟨ 2 & 1 & whisk⊙-conv-r (⊙∘-α-comp k h g) ⟩
    ap (λ m → k ⊙∘ m) (⊙-comp-to-== (⊙∘-α-comp h g f)) ◃∙
    ⊙-comp-to-== (⊙∘-α-comp k (h ⊙∘ g) f) ◃∙
    ap (λ m → m ⊙∘ f) (⊙-comp-to-== (⊙∘-α-comp k h g)) ◃∎ ∎ₛ
  hom-trunc Ptd02-bicat {X₁ , c₁ , _} {X₂ , _ , t₂} = ptd-conn-tr-hom-tr X₁ X₂ c₁ t₂

instance
  Ptd02-bicat-instance : ∀ {i} → BicatStr i (Ptd02 i)
  Ptd02-bicat-instance {i} = Ptd02-bicat {i}
