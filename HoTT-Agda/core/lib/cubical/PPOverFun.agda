{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathFunctor
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
      → Π (B₁ x) (λ b →  f b == g (transport B₁ p b) [ B₂ ↓ p ])
      → f == g [ C ↓ p ]
    po-ext idp h = λ= h

    ppo-ext : {p₁ p₂ : x == y} (q : p₁ == p₂)
      (α₁ : Π (B₁ x) (λ b →  f b == g (transport B₁ p₁ b) [ B₂ ↓ p₁ ]))
      (α₂ : Π (B₁ x) (λ b →  f b == g (transport B₁ p₂ b) [ B₂ ↓ p₂ ]))
      → Π (B₁ x)
        (λ b → PPOver q (po-fun-↓ap q (λ p → g (transport B₁ p b)) (α₁ b)) (α₂ b))
      → PPOver q (po-ext p₁ α₁) (po-ext p₂ α₂)
    ppo-ext {p₁ = idp} idp α₁ α₂ h = ap λ= (λ= h)
