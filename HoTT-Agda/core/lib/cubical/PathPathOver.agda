{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

module lib.cubical.PathPathOver where

module _ {i j} {A : Type i} {B : A → Type j} where

  -- fillers of an open 3-dim box between pathovers
  PathPathOver : {x y : A} {p₁ p₂ : x == y} (q : p₁ == p₂) {u : B x} {v : B y}
    (d : u == v [ B ↓ p₁ ]) (e : u == v [ B ↓ p₂ ]) → Type j
  PathPathOver {p₁ = idp} idp d e = d == e

  apdd-∙ᵈ : (f : (a : A) → B a) {x y z : A} {τ₃ : x == z} (τ₁ : x == y) (τ₂ : y == z)
    (p : τ₁ ∙ τ₂ == τ₃) → PathPathOver p (apd f τ₁ ∙ᵈ apd f τ₂) (apd f τ₃)
  apdd-∙ᵈ f {τ₃ = idp} idp τ₂ idp = idp

  -- associativity of pathovers (similar to ∙ᵈ-assoc in PathGroupoid.agda)
  ∙ᵈ-assoc-PPO : {x y z w : A} {p₁ : x == y} {p₂ : y == z} {p₃ : z == w}
    {b₀ : B x} {b₁ : B y} {b₂ : B z} {b₃ : B w}
    (d₁ : b₀ == b₁ [ B ↓ p₁ ]) (d₂ : b₁ == b₂ [ B ↓ p₂ ]) (d₃ : b₂ == b₃ [ B ↓ p₃ ])
    → PathPathOver (∙-assoc p₁ p₂ p₃) ((d₁ ∙ᵈ d₂) ∙ᵈ d₃) (d₁ ∙ᵈ (d₂ ∙ᵈ d₃))
  ∙ᵈ-assoc-PPO {p₁ = idp} {p₂ = idp} {p₃ = idp} d₁ d₂ d₃ = ∙-assoc d₁ d₂ d₃

  -- applying a family of pathovers over paths in X to a path in X  

  -- operations on PathPathOver

  infixr 50 _∙ᶜ_
  _∙ᶜ_ : {x y : A} {p₁ p₂ p₃ : x == y} (q₁ : p₁ == p₂) (q₂ : p₂ == p₃)
    {u : B x} {v : B y}
    (d : u == v [ B ↓ p₁ ]) (e : u == v [ B ↓ p₂ ]) (j : u == v [ B ↓ p₃ ])
    → PathPathOver q₁ d e → PathPathOver q₂ e j → PathPathOver (q₁ ∙ q₂) d j
  _∙ᶜ_ {p₁ = idp} idp idp _ _ _ po₁ po₂ = po₁ ∙ po₂

  !ᶜ : {x y : A} {p₁ p₂ : x == y} (q : p₁ == p₂) {u : B x} {v : B y}
    (d : u == v [ B ↓ p₁ ]) (e : u == v [ B ↓ p₂ ])
    → PathPathOver q d e → PathPathOver (! q) e d
  !ᶜ {p₁ = idp} idp _ _ po = ! po

  ap-∙-preᶜ : {x y z : A} {p₁ p₂ : x == y} {r : z == x} (q : p₁ == p₂)
    {u : B x} {v : B y} {w : B z}
    (d₁ : u == v [ B ↓ p₁ ]) (d₂ : u == v [ B ↓ p₂ ]) (e : w == u [ B ↓ r ])
    → PathPathOver q d₁ d₂ → PathPathOver (ap (λ p → r ∙ p) q) (e ∙ᵈ d₁) (e ∙ᵈ d₂)
  ap-∙-preᶜ {p₁ = idp} {r = idp} idp _ _ e po = ap (λ p → e ∙ p) po
  
  ap-∙-postᶜ : {x y z : A} {p₁ p₂ : x == y} {r : y == z} (q : p₁ == p₂)
    {u : B x} {v : B y} {w : B z}
    (d₁ : u == v [ B ↓ p₁ ]) (d₂ : u == v [ B ↓ p₂ ]) (e : v == w [ B ↓ r ])
    → PathPathOver q d₁ d₂ → PathPathOver (ap (λ p → p ∙ r) q) (d₁ ∙ᵈ e) (d₂ ∙ᵈ e)
  ap-∙-postᶜ {p₁ = idp} {r = idp} idp _ _ e po = ap (λ p → p ∙ e) po

-- describe PathPathOver for B₁ : A → Type j , B₂ : A → Type k , C = λ a → (B₁ a → B₂ a)

-- PathPathPathOver (fillers of an open 4-dim box between double pathovers)
