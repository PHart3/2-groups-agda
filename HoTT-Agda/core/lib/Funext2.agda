{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Equivalence
open import lib.NType
open import lib.Function
open import lib.Funext
open import lib.types.Sigma
open import lib.types.Pi

-- function extensionality for functions of higher arity

module lib.Funext2 {i} {A : Type i} where

  module _ {j} where

    Π-iter : (n : ℕ-ₚ) (P : ×⦅ n ⦆ A → Type j) → Type (lmax i j)
    Π-iter I P = Π A P
    Π-iter (S n) P = Π A (λ a → Π-iter n (curry P a))

    infixr 80 _∼^_
    _∼^_ : {n : ℕ-ₚ} {P : ×⦅ n ⦆ A → Type j} → Π-iter n P → Π-iter n P → Type (lmax i j)
    _∼^_ {n = I} f g = f ∼ g
    _∼^_ {n = S n} f g = (a : A) → _∼^_ {n = n} (f a) (g a)

    app=-equiv-iter : {n : ℕ-ₚ} {P : ×⦅ n ⦆ A → Type j} {f g : Π-iter n P} → (f == g) ≃ (f ∼^ g)
    app=-equiv-iter {I} {f = f} {g = g} = app=-equiv
    app=-equiv-iter {S n} {f = f} {g = g} = lemma ∘e app=-equiv
      where
        lemma : (f ∼ g) ≃ Π A (λ a → f a ∼^ g a)
        lemma = Π-emap-r (λ a → app=-equiv-iter {n} {f = f a} {g = g a})        

    funhom-iter-contr : (n : ℕ-ₚ) {P : ×⦅ n ⦆ A → Type j} (f : Π-iter n P) → is-contr (Σ (Π-iter n P) (λ g → f ∼^ g))
    funhom-iter-contr _ f = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv-iter)) {{pathfrom-is-contr f}}

    funhom-iter-contr-to : (n : ℕ-ₚ) {P : ×⦅ n ⦆ A → Type j} (f : Π-iter n P) → is-contr (Σ (Π-iter n P) (λ g → g ∼^ f))
    funhom-iter-contr-to _ f = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv-iter)) {{pathto-is-contr f}}
