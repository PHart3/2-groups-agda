{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
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
  apᶜ² {q = idp} c₁ c₂ po = ! c₁ ∙ po ∙ c₂

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

  -- PPOver for a family of 1-types is always inhabited.
  

module _ {i j k} {A : Type i} {B : A → Type j} {X : Type k} where

  -- applying an X-indexed family of pathovers to a path in X  
  apd-po : {a₁ a₂ : A} {p : X → a₁ == a₂} {u : B a₁} {v : B a₂}
    (f : (x : X) → u == v [ B ↓ p x ]) {x₁ x₂ : X} (q : x₁ == x₂)
    → PPOver (ap p q) (f x₁) (f x₂)
  apd-po f idp = idp

-- behavior of higher-dimensional pathovers for constant type families

module _ {i j} {A : Type i} {B : Type j} where

  ppo-cst-in-∙-aux : {y z : A} (p₁ : y == z) (p₂ : y == z)
    {a b c : B} (τ₁ : a == b) {τ₂ : b == c}
    → τ₁ ∙ᵈ ↓-cst-in {p = p₁} τ₂ == ↓-cst-in (τ₁ ∙ τ₂)
  ppo-cst-in-∙-aux idp p₂ τ₁ = idp

  ppo-cst-in-∙ : {x y z : A} (p₁ : x == y) {p₂ : y == z}
    {p₃ : x == z} {a b c : B} {τ₁ : a == b} {τ₂ : b == c}
    {τ₃ : a == c} (q : p₁ ∙ p₂ == p₃) (r : τ₁ ∙ τ₂ == τ₃)
    → PPOver q (↓-cst-in {p = p₁} τ₁ ∙ᵈ ↓-cst-in τ₂) (↓-cst-in τ₃)
  ppo-cst-in-∙ idp {p₂} {p₃} {τ₁ = τ₁} idp idp = ppo-cst-in-∙-aux p₂ p₃ τ₁

  pppo-cst-in-word-aux2 : {v₁ v₂ v₃ : B} (c₁ : v₁ == v₂) {c₂ : v₂ == v₃} {c₃ : v₃ == v₃}
    {a₀ a₁ a₂ a₃ : A} (d₁ : a₀ == a₁) {d₂ : a₁ == a₂} {d₃ : a₂ == a₃}
    {q : (d₁ ∙ d₂) ∙ d₃ == d₁ ∙ (d₂ ∙ d₃)}
    (r : ∙-assoc d₁ d₂ d₃ == q)
    → 
    PPPOver (ap (λ p → p ∙ idp) r)
    (∙ᵈ-assoc-ppo (↓-cst-in {p = d₁} c₁) (↓-cst-in c₂) (↓-cst-in c₃) ∙ᶜ
     ap-∙-preᶜ (↓-cst-in {p = d₁} c₁) (ppo-cst-in-∙ d₂ idp idp) ∙
     ppo-cst-in-∙ d₁ idp idp)
    (ap-∙-postᶜ (↓-cst-in c₃) (ppo-cst-in-∙ d₁ idp idp) ∙ᶜ
     ppo-cst-in-∙ (d₁ ∙ d₂) q (∙-assoc c₁ c₂ c₃ ∙ idp) ∙ᶜ idp)
  pppo-cst-in-word-aux2 idp {c₂ = idp} idp {d₂ = idp} {d₃ = idp} idp = idp

  pppo-cst-in-word-aux : {v : B} (c₁ c₂ c₃ : v == v)
    {a : A} (d₁ : a == a) {d₂ d₃ d₄ d₅ d₆ : a == a}
    (q₁ : d₁ ∙ d₂ == d₃) (q₂ : d₂ ∙ d₅ == d₄)
    (q₃ : d₁ ∙ d₄ == d₆) (q₄ : d₃ ∙ d₅ == d₆)
    {m : v == v} (e₃ : c₁ ∙ c₂ ∙ c₃ == m) {e₄ : (c₁ ∙ c₂) ∙ c₃ == m}
    (r : ∙-assoc d₁ d₂ d₅ ∙ ap (λ s → d₁ ∙ s) q₂ ∙ q₃
         == ap (λ z → z ∙ d₅) q₁ ∙ q₄ ∙ idp)
    → 
    ∙-assoc c₁ c₂ c₃ ∙ e₃ == e₄ →
    PPPOver r
    (∙ᵈ-assoc-ppo (↓-cst-in {p = d₁} c₁) (↓-cst-in c₂) (↓-cst-in c₃) ∙ᶜ
     ap-∙-preᶜ (↓-cst-in c₁) (ppo-cst-in-∙ d₂ q₂ idp) ∙ᶜ
     ppo-cst-in-∙ d₁ q₃ e₃)
    (ap-∙-postᶜ (↓-cst-in c₃) (ppo-cst-in-∙ d₁ q₁ idp) ∙ᶜ
     ppo-cst-in-∙ d₃ q₄ e₄ ∙ᶜ idp)
  pppo-cst-in-word-aux c₁ c₂ c₃ d₁ {d₂} idp idp idp q₄ idp r idp =
    ∙-id-ind
      (λ r → PPPOver r
        (∙ᵈ-assoc-ppo (↓-cst-in {p = d₁} c₁) (↓-cst-in c₂) (↓-cst-in c₃) ∙ᶜ
        ap-∙-preᶜ (↓-cst-in {p = d₁} c₁) (ppo-cst-in-∙ d₂ idp idp) ∙
        ppo-cst-in-∙ d₁ idp idp)
        (ap-∙-postᶜ (↓-cst-in c₃) (ppo-cst-in-∙ d₁ idp idp) ∙ᶜ
          ppo-cst-in-∙ (d₁ ∙ d₂) q₄ (∙-assoc c₁ c₂ c₃ ∙ idp) ∙ᶜ idp))
      (pppo-cst-in-word-aux2 c₁ d₁) r 

  pppo-cst-in-word : ∀ {k} {X : Type k} {a : A} {x y z w u t₁ t₂ : X}
    (τ : X → a == a) {v : B} (f : X → v == v)
    (ρ : t₁ == t₂)
    (q₁ : τ x ∙ τ y == τ w) (q₂ : τ y ∙ τ z == τ u)
    (q₃ : τ x ∙ τ u == τ t₁) (q₄ : τ w ∙ τ z == τ t₂)
    {d₁ d₂ : v == v} (e₁ : f x ∙ f y == d₁) (e₂ : f y ∙ f z == d₂)
    (e₃ : f x ∙ d₂ == f t₁) (e₄ : d₁ ∙ f z == f t₂)
    (r : ∙-assoc (τ x) (τ y) (τ z) ∙ ap (λ s →  τ x ∙ s) q₂ ∙ q₃
         == ap (λ s → s ∙ τ z) q₁ ∙ q₄ ∙ ! (ap τ ρ))
    →
    ∙-assoc (f x) (f y) (f z) ∙ ap (λ p → f x ∙ p) e₂ ∙ e₃
      ==
    ap (λ p → p ∙ f z) e₁ ∙ e₄ ∙' ! (ap f ρ)
    → 
    PPPOver r
    (∙ᵈ-assoc-ppo (↓-cst-in {p = τ x} (f x)) (↓-cst-in {p = τ y} (f y)) (↓-cst-in {p = τ z} (f z))
     ∙ᶜ
     ap-∙-preᶜ (↓-cst-in (f x)) (ppo-cst-in-∙ (τ y) q₂ e₂)
     ∙ᶜ
     ppo-cst-in-∙ (τ x) q₃ e₃)
    (ap-∙-postᶜ (↓-cst-in (f z)) (ppo-cst-in-∙ (τ x) q₁ e₁)
     ∙ᶜ
     ppo-cst-in-∙ (τ w) q₄ e₄
     ∙ᶜ
     !ᶜ (apd-po {p = τ} (λ s → ↓-cst-in (f s)) ρ))
  pppo-cst-in-word {x = x} {y} {z} τ f idp q₁ q₂ q₃ q₄ idp idp e₃ e₄ r =
    pppo-cst-in-word-aux (f x) (f y) (f z) (τ x) q₁ q₂ q₃ q₄ e₃ r

  ppo-cst-in-∙ᵈ : (f : A → B) {a₀ a a₁ : A} (p₁ : a₀ == a) {p₂ : a == a₁}
    {p₃ : a₀ == a₁} {q₁ : f a₀ == f a} {q₂ : f a == f a₁}
    {q₃ : f a₀ == f a₁} (ρ : p₁ ∙ p₂ == p₃) (τ : q₁ ∙ q₂ == q₃)
    (r₁ : apd f p₁ == ↓-cst-in q₁) (r₂ : apd f p₂ == ↓-cst-in q₂)
    (r₃ : apd f p₃ == ↓-cst-in q₃) →
    apdd-∙ᵈ f p₁ p₂ ρ
      ==
    apᶜ² (! r₁ ∙ᵈ= ! r₂) (! r₃) (ppo-cst-in-∙ p₁ ρ τ)
    →
    τ ==
    ! (pair=-curry (_∙_) (apd=cst-in r₁) (apd=cst-in r₂)) ∙
    ∙-ap f p₁ p₂ ∙ ap (ap f) ρ ∙ (apd=cst-in r₃) 
  ppo-cst-in-∙ᵈ f {a₀} idp {p₂ = idp} idp idp r₁ r₂ r₃ = lemma r₁ r₂ r₃ 
    where
      lemma : {z₁ z₂ : f a₀ == f a₀}
        (s₁ : idp == z₁) (s₂ : idp == z₂) (s₃ : idp == z₁ ∙ z₂) →
        idp == ! (_∙ᵈ=_ {A = A} {B = λ _ → B} {x = a₀} (! s₁) (! s₂)) ∙ ! s₃ →
        idp == ! (pair=-curry _∙_ s₁ s₂) ∙ s₃
      lemma idp idp s₃ v = ap ! v ∙ !-! s₃
