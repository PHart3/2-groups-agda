{-# OPTIONS --without-K --rewriting --confluence-check #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.CommutingSquare
open import lib.types.Paths

module lib.types.Pushout where

module _ {i j k} where

  postulate  -- HIT
    Pushout : (d : Span {i} {j} {k}) → Type (lmax (lmax i j) k)

  module _ {d : Span} where

    postulate  -- HIT
      left : Span.A d → Pushout d
      right : Span.B d → Pushout d
      glue : (c : Span.C d) → left (Span.f d c) == right (Span.g d c)

  module PushoutElim {d : Span} {l} {P : Pushout d → Type l}
    (left* : (a : Span.A d) → P (left a))
    (right* : (b : Span.B d) → P (right b))
    (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c) [ P ↓ glue c ]) where

    postulate  -- HIT
      f : Π (Pushout d) P
      left-β : ∀ a → f (left a) ↦ left* a
      right-β : ∀ b → f (right b) ↦ right* b
    {-# REWRITE left-β #-}
    {-# REWRITE right-β #-}

    postulate  -- HIT
      glue-β : (c : Span.C d) → apd f (glue c) == glue* c

Pushout-elim = PushoutElim.f

module PushoutRec {i j k} {d : Span {i} {j} {k}} {l} {D : Type l}
  (left* : Span.A d → D) (right* : Span.B d → D)
  (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c)) where

  private
    module M = PushoutElim left* right* (λ c → ↓-cst-in (glue* c))

  f : Pushout d → D
  f = M.f

  glue-β : (c : Span.C d) → ap f (glue c) == glue* c
  glue-β c = apd=cst-in {f = f} (M.glue-β c)

Pushout-rec = PushoutRec.f

Pushout-rec-η : ∀ {i j k} {d : Span {i} {j} {k}} {l} {D : Type l} (f : Pushout d → D)
  → Pushout-rec (f ∘ left) (f ∘ right) (ap f ∘ glue) ∼ f
Pushout-rec-η f = Pushout-elim (λ _ → idp) (λ _ → idp)
  (λ c → ↓-='-in' $ ! $ PushoutRec.glue-β (f ∘ left) (f ∘ right) (ap f ∘ glue) c)

PushoutMapEq : ∀ {i j k} {d : Span {i} {j} {k}} {l} {D : Type l} (h₁ h₂ : Pushout d → D)
  → (p₁ : h₁ ∘ left ∼ h₂ ∘ left) (p₂ : h₁ ∘ right ∼ h₂ ∘ right)
  → ((c : Span.C d) → (! (ap h₁ (glue c)) ∙ p₁ (Span.f d c)) ∙ ap h₂ (glue c) == p₂ (Span.g d c))
  → h₁ ∼ h₂
PushoutMapEq {d = d} h₁ h₂ p₁ p₂ =
  λ S → Pushout-elim p₁ p₂ λ c →
    from-transp (λ x → h₁ x == h₂ x) (glue c)
    (transp-pth-l (glue c) (p₁ (Span.f d c)) ∙ S c)

module _ {ℓ} {A : Type ℓ} where

  !-∙→= : {x y : A} (p : x == y) (q : x == y) → ! p ∙ q == idp → p == q
  !-∙→= idp q e = ! e

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f g : A → B) where

  transp-pth-reord : {x y : A} (p : x == y) (p₁ : f x == g x) (p₂ : f y == g y)
    → ! p₁ ∙ ap f p ∙ p₂ == ap g p → transport (λ z → f z == g z) p p₁ == p₂
  transp-pth-reord idp p₁ p₂ = !-∙→= p₁ p₂

PushoutMapEq-v2 : ∀ {i j k} {d : Span {i} {j} {k}} {l} {D : Type l} (h₁ h₂ : Pushout d → D)
  → (p₁ : h₁ ∘ left ∼ h₂ ∘ left) (p₂ : h₁ ∘ right ∼ h₂ ∘ right)
  → ((c : Span.C d) → ! (p₁ (Span.f d c)) ∙ ap h₁ (glue c) ∙ p₂ (Span.g d c) == ap h₂ (glue c))
  → h₁ ∼ h₂
PushoutMapEq-v2 {d = d} h₁ h₂ p₁ p₂ =
  λ S → Pushout-elim p₁ p₂ λ c →
    from-transp (λ x → h₁ x == h₂ x) (glue c)
    (transp-pth-reord h₁ h₂ (glue c) (p₁ (Span.f d c)) (p₂ (Span.g d c)) (S c))

module PushoutMap {i₀ j₀ k₀ i₁ j₁ k₁} {span₀ : Span {i₀} {j₀} {k₀}} {span₁ : Span {i₁} {j₁} {k₁}} (span-map : SpanMap-Rev span₀ span₁)
  = PushoutRec {d = span₀} {D = Pushout span₁}
    (left ∘ SpanMap-Rev.hA span-map) (right ∘ SpanMap-Rev.hB span-map)
    (λ x → ! (ap left (SpanMap-Rev.f-commutes span-map □$ x)) ∙ glue (SpanMap-Rev.hC span-map x) ∙
      ap right (SpanMap-Rev.g-commutes span-map □$  x))

_⊔^[_]_/_ : ∀ {i j k} (A : Type i) (C : Type k) (B : Type j)
  (fg : (C → A) × (C → B)) → Type (lmax (lmax i j) k)
A ⊔^[ C ] B  / (f , g) = Pushout (span A B C f g)

⊙Pushout : ∀ {i j k} (d : ⊙Span {i} {j} {k}) → Ptd _
⊙Pushout d = ⊙[ Pushout (⊙Span-to-Span d) , left (pt (⊙Span.X d)) ]

module _ {i j k} (d : ⊙Span {i} {j} {k}) where

  open ⊙Span d

  ⊙left : X ⊙→ ⊙Pushout d
  ⊙left = (left , idp)

  ⊙right : Y ⊙→ ⊙Pushout d
  ⊙right =
    (right , ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f))

  ⊙glue : (⊙left ⊙∘ f) == (⊙right ⊙∘ g)
  ⊙glue = pair=
    (λ= glue)
    (↓-app=cst-in $
      ap left (snd f) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap left (snd f)
        =⟨ lemma (glue (pt Z)) (ap right (snd g)) (ap left (snd f)) ⟩
      glue (pt Z) ∙ ap right (snd g)
      ∙ ! (ap right (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f)
        =⟨ !-ap right (snd g)
           |in-ctx (λ w → glue (pt Z) ∙ ap right (snd g) ∙ w
                          ∙ ! (glue (pt Z)) ∙' ap left (snd f)) ⟩
      glue (pt Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f)
        =⟨ ! (app=-β glue (pt Z))
           |in-ctx (λ w → w ∙ ap right (snd g) ∙ ap right (! (snd g))
                            ∙ ! (glue (pt Z)) ∙' ap left (snd f)) ⟩
      app= (λ= glue) (pt Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f) =∎)
    where
    lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : y == z) (r : x == w)
      → r == p ∙ q ∙ ! q ∙ ! p ∙' r
    lemma idp idp idp = idp

⊙pushout-J : ∀ {i j k l} (P : ⊙Span → Type l)
  → ({A : Type i} {B : Type j} (Z : Ptd k) (f : de⊙ Z → A) (g : de⊙ Z → B)
     → P (⊙span ⊙[ A , f (pt Z) ] ⊙[ B , g (pt Z) ] Z (f , idp) (g , idp)))
  → ((ps : ⊙Span) → P ps)
⊙pushout-J P t (⊙span ⊙[ _ , ._ ] ⊙[ _ , ._ ] Z (f , idp) (g , idp)) = t Z f g
