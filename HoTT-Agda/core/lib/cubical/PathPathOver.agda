{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathOver

module lib.cubical.PathPathOver where

module _ {i j} {A : Type i} {B : A → Type j} where

  -- fillers of an open 3-dim box between pathovers
  PPOver : {x y : A} {p₁ p₂ : x == y} (q : p₁ == p₂) {u : B x} {v : B y}
    (d : u == v [ B ↓ p₁ ]) (e : u == v [ B ↓ p₂ ]) → Type j
  PPOver idp d e = d == e

  apᶜ² : {x y : A} {p₁ p₂ : x == y} {q : p₁ == p₂} {u : B x} {v : B y}
    {d₁ d₂ : u == v [ B ↓ p₁ ]} {e₁ e₂ : u == v [ B ↓ p₂ ]}
    → d₁ == d₂ → e₁ == e₂ → PPOver q d₁ e₁ → PPOver q d₂ e₂
  apᶜ² idp idp po = po

  apdd-∙ᵈ : (f : (a : A) → B a) {x y z : A} {τ₃ : x == z} (τ₁ : x == y) (τ₂ : y == z)
    (p : τ₁ ∙ τ₂ == τ₃) → PPOver p (apd f τ₁ ∙ᵈ apd f τ₂) (apd f τ₃)
  apdd-∙ᵈ f {τ₃ = idp} idp τ₂ idp = idp

  -- associativity of pathovers (similar to ∙ᵈ-assoc in PathGroupoid.agda)
  ∙ᵈ-assoc-ppo : {x y z w : A} {p₁ : x == y} {p₂ : y == z} {p₃ : z == w}
    {b₀ : B x} {b₁ : B y} {b₂ : B z} {b₃ : B w}
    (d₁ : b₀ == b₁ [ B ↓ p₁ ]) (d₂ : b₁ == b₂ [ B ↓ p₂ ]) (d₃ : b₂ == b₃ [ B ↓ p₃ ])
    → PPOver (∙-assoc p₁ p₂ p₃) ((d₁ ∙ᵈ d₂) ∙ᵈ d₃) (d₁ ∙ᵈ (d₂ ∙ᵈ d₃))
  ∙ᵈ-assoc-ppo {p₁ = idp} {p₂ = idp} {p₃ = idp} d₁ d₂ d₃ = ∙-assoc d₁ d₂ d₃

  -- basic operations on PPOver

  infixr 50 _∙ᶜ_
  _∙ᶜ_ : {x y : A} {p₁ p₂ p₃ : x == y} {q₁ : p₁ == p₂} {q₂ : p₂ == p₃}
    {u : B x} {v : B y}
    {d : u == v [ B ↓ p₁ ]} {e : u == v [ B ↓ p₂ ]} {j : u == v [ B ↓ p₃ ]}
    → PPOver q₁ d e → PPOver q₂ e j → PPOver (q₁ ∙ q₂) d j
  _∙ᶜ_ {q₁ = idp} {q₂ = idp} po₁ po₂ = po₁ ∙ po₂

  !ᶜ : {x y : A} {p₁ p₂ : x == y} {q : p₁ == p₂} {u : B x} {v : B y}
    {d : u == v [ B ↓ p₁ ]} {e : u == v [ B ↓ p₂ ]}
    → PPOver q d e → PPOver (! q) e d
  !ᶜ {q = idp} po = ! po

  ap-∙-preᶜ : {x y z : A} {p₁ p₂ : x == y} {r : z == x} {q : p₁ == p₂}
    {u : B x} {v : B y} {w : B z}
    {d₁ : u == v [ B ↓ p₁ ]} {d₂ : u == v [ B ↓ p₂ ]} (e : w == u [ B ↓ r ])
    → PPOver q d₁ d₂ → PPOver (ap (λ p → r ∙ p) q) (e ∙ᵈ d₁) (e ∙ᵈ d₂)
  ap-∙-preᶜ {p₁ = idp} {r = idp} {q = idp} e po = ap (λ p → e ∙ p) po
  
  ap-∙-postᶜ : {x y z : A} {p₁ p₂ : x == y} {r : y == z} {q : p₁ == p₂}
    {u : B x} {v : B y} {w : B z}
    {d₁ : u == v [ B ↓ p₁ ]} {d₂ : u == v [ B ↓ p₂ ]} (e : v == w [ B ↓ r ])
    → PPOver q d₁ d₂ → PPOver (ap (λ p → p ∙ r) q) (d₁ ∙ᵈ e) (d₂ ∙ᵈ e)
  ap-∙-postᶜ {p₁ = idp} {r = idp} {q = idp} e po = ap (λ p → p ∙ e) po

  -- fillers of an open 4-dim box between double pathovers
  PPPOver : {x y : A} {p₁ p₂ : x == y} {q₁ q₂ : p₁ == p₂} {u : B x} {v : B y}
    (r : q₁ == q₂) {d : u == v [ B ↓ p₁ ]} {e : u == v [ B ↓ p₂ ]} 
    → PPOver q₁ d e → PPOver q₂ d e → Type j
  PPPOver idp po₁ po₂ = po₁ == po₂

module _ {i j k} {A : Type i} {B : A → Type j} {X : Type k} where

  -- applying an X-indexed family of pathovers to a path in X  
  apd-po : {a₁ a₂ : A} {p : (x : X) → a₁ == a₂} {u : B a₁} {v : B a₂}
    (f : (x : X) → u == v [ B ↓ p x ]) {x₁ x₂ : X} (q : x₁ == x₂)
    → PPOver (ap p q) (f x₁) (f x₂)
  apd-po f idp = idp

module _ {i j} {A : Type i} {B : Type j} where

  ppo-cst-in-∙ : {x y z : A} {p₁ : x == y} {p₂ : y == z}
    {p₃ : x == z} {a b c : B} {τ₁ : a == b} {τ₂ : b == c}
    {τ₃ : a == c} (q : p₁ ∙ p₂ == p₃) (r : τ₁ ∙ τ₂ == τ₃)
    → PPOver q (↓-cst-in {p = p₁} τ₁ ∙ᵈ ↓-cst-in τ₂) (↓-cst-in τ₃)
  ppo-cst-in-∙ {p₁ = idp} {p₂ = idp} {τ₁ = idp} {τ₂ = idp} idp idp = idp

-- Describe PPOver for B₁ : A → Type j , B₂ : A → Type k , C = λ a → (B₁ a → B₂ a)
