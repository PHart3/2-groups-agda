{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2

-- [Subtype] is defined in lib.NType.

module lib.types.Subtype where

open SubtypeProp

infix 40 _⊆_
_⊆_ : ∀ {i j₁ j₂} {A : Type i} → SubtypeProp {A = A} {j₁} → SubtypeProp {A = A} {j₂}
  → Type (lmax i (lmax j₁ j₂))
P₁ ⊆ P₂ = ∀ a → prop P₁ a → prop P₂ a

infix 80 _∘sub_
_∘sub_ : ∀ {i j k} {A : Type i} {B : Type j}
  → SubtypeProp {A = B} {k} → (A → B) → SubtypeProp {A = A} {k}
_∘sub_{A = A} P f = subtypeprop ((prop P) ∘ f)
