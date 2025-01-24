{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Funext
open import lib.cubical.PathPathOver

module lib.cubical.PPOverFun where

module _ {i j k} {A : Type i} {B₁ : A → Type j} {B₂ : A → Type k} where

  {-
    behavior of higher-dimensional pathovers
    for the type family λ a → (B₁ a → B₂ a)
  -}
  
  private
    C : A → Type (lmax j k)
    C = λ a → (B₁ a → B₂ a)

  module _ {x y : A} {f : B₁ x → B₂ x} {g : B₁ y → B₂ y} where

    po-ext : (p : x == y) 
      → Π (B₁ x) (λ b →  g (transport B₁ p b) == transport B₂ p (f b))
      → f == g [ C ↓ p ]
    po-ext idp h = λ= (! ∘ h)

    ppo-ext : {p₁ p₂ : x == y} (q : p₁ == p₂)
      (α₁ : Π (B₁ x) (λ b →  g (transport B₁ p₁ b) == transport B₂ p₁ (f b)))
      (α₂ : Π (B₁ x) (λ b →  g (transport B₁ p₂ b) == transport B₂ p₂ (f b)))
      → Π (B₁ x) (λ b →
        ap g (ap (λ p → transport B₁ p b) q) ◃∙ α₂ b ◃∎
          =ₛ
        α₁ b ◃∙ ap (λ p → transport B₂ p (f b)) q ◃∎)
      → PPOver q (po-ext p₁ α₁) (po-ext p₂ α₂)
    ppo-ext {p₁ = idp} idp α₁ α₂ h =
      ap λ= (λ= λ z → ap ! (! (∙-unit-r (α₁ z)) ∙ ! (=ₛ-out (h z)) )) 
