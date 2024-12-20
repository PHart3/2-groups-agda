{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

module lib.cubical.PathPathOver where

module _ {i j} {A : Type i} {B : A → Type j} where

  PathPathOver : {x y : A} {p₁ p₂ : x == y} (q : p₁ == p₂) {u : B x} {v : B y}
    (d : u == v [ B ↓ p₁ ]) (e : u == v [ B ↓ p₂ ]) → Type j
  PathPathOver {p₁ = idp} idp d e = d == e

  apdd-∙ᵈ : (f : (a : A) → B a) {x y z : A} {τ₃ : x == z} (τ₁ : x == y) (τ₂ : y == z)
    (p : τ₁ ∙ τ₂ == τ₃) → PathPathOver p (apd f τ₁ ∙ᵈ apd f τ₂) (apd f τ₃)
  apdd-∙ᵈ f {τ₃ = idp} idp τ₂ idp = idp
