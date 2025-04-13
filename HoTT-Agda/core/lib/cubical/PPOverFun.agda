{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.Funext
open import lib.path-seq.Concat
open import lib.path-seq.Ap
open import lib.path-seq.Reasoning
open import lib.cubical.PathPathOver

module lib.cubical.PPOverFun where

module _ {i j k} {A : Type i} {B₁ : A → Type j} {B₂ : A → Type k} where

  {-
    behavior of higher-dimensional pathovers
    for the type family λ a → (B₁ a → B₂ a)

    This provides a way of building input
    data for induction on the delooping of
    a 2-group.
  -}
  
  private
    C : A → Type (lmax j k)
    C = λ a → (B₁ a → B₂ a)

  module _ {x y : A} {f : B₁ x → B₂ x} {g : B₁ y → B₂ y} where

    po-ext : (p : x == y) 
      → Π (B₁ x) (λ b → g (transport B₁ p b) =-= transport B₂ p (f b))
      → f == g [ C ↓ p ]
    po-ext idp h = λ= (λ z → ! (↯ (h z)))

  module _ {x y z : A} {f : B₁ x → B₂ x} {g : B₁ y → B₂ y} {h : B₁ z → B₂ z} where

    ppo-ext : {p₁ : x == y} {p₂ : y == z} {p₃ : x == z} (q : p₁ ∙ p₂ == p₃)
      (α₁ : Π (B₁ x) (λ b → g (transport B₁ p₁ b) =-= transport B₂ p₁ (f b)))
      (α₂ : Π (B₁ y) (λ b → h (transport B₁ p₂ b) =-= transport B₂ p₂ (g b)))
      (α₃ : Π (B₁ x) (λ b → h (transport B₁ p₃ b) =-= transport B₂ p₃ (f b)))
      → Π (B₁ x) (λ b →
        ! (ap h (transp-∙ p₁ p₂ b)) ◃∙
        ap h (ap (λ p → transport B₁ p b) q) ◃∙
        α₃ b
          =ₛ
        α₂ (transport B₁ p₁ b) ∙∙
        (ap-seq (transport B₂ p₂) (α₁ b) ∙∙
        ! (transp-∙ p₁ p₂ (f b)) ◃∙
        ap (λ p → transport B₂ p (f b)) q ◃∎) )
      → PPOver q (po-ext p₁ α₁ ∙ᵈ po-ext p₂ α₂) (po-ext {g = h} p₃ α₃)
    ppo-ext {p₁ = idp} {p₂ = idp} idp α₁ α₂ α₃ h =
      =ₛ-out (∙-λ= (! ∘ ↯ ∘ α₁) (! ∘ ↯ ∘ α₂)) ∙
      ap λ= (λ= (λ z → ! (=ₛ-out (aux z))))
      where
        aux : (z : B₁ x) → ! (↯ (α₃ z)) ◃∎ =ₛ ! (↯ (α₁ z)) ◃∙ ! (↯ (α₂ z)) ◃∎
        aux z = 
          ! (↯ (α₃ z)) ◃∎
            =ₛ₁⟨ ap ! (! (↯-∙∙ (idp ◃∎) (α₃ z))) ⟩
          ! (↯ (idp ◃∙ α₃ z)) ◃∎
            =ₛ₁⟨ ap ! (=ₛ-out (h z)) ⟩
          ! (↯ (α₂ z ∙∙ ap-seq (λ x → x) (α₁ z) ∙∙ idp ◃∙ idp ◃∎)) ◃∎
            =ₛ₁⟨ ap ! (↯-∙∙ (α₂ z) (ap-seq (λ x → x) (α₁ z) ∙∙ idp ◃∙ idp ◃∎)) ⟩
          _
            =ₛ₁⟨ ap ! (ap (λ q → ↯ (α₂ z) ∙ q)
                   (↯-∙∙ (ap-seq (λ x → x) (α₁ z)) (idp ◃∙ idp ◃∎))) ⟩
          _
            =ₛ₁⟨ ap (λ q → ! (↯ (α₂ z) ∙ q ∙ idp)) (=ₛ-out (∙-ap-seq (λ x → x) (α₁ z))) ⟩
          ! (↯ (α₂ z) ∙ ap (λ x → x) (↯ (α₁ z)) ∙ idp) ◃∎
            =ₛ₁⟨ ap (λ q → ! (↯ (α₂ z) ∙ q)) (
                   ∙-unit-r (ap (λ x → x) (↯ (α₁ z))) ∙ ap-idf (↯ (α₁ z))) ⟩
          ! (↯ (α₂ z) ∙ ↯ (α₁ z)) ◃∎
            =ₛ⟨ !-∙◃ (↯ (α₂ z)) (↯ (α₁ z)) ⟩
          ! (↯ (α₁ z)) ◃∙ ! (↯ (α₂ z)) ◃∎ ∎ₛ
