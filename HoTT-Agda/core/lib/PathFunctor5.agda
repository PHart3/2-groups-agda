{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathFunctor4
open import lib.path-seq.Ap
open import lib.path-seq.Inversion
open import lib.path-seq.Concat
open import lib.path-seq.Reasoning

module lib.PathFunctor5 where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (g₁ : B → C) (g₂ : D → C)
  {f₁ : A → C} {f₂ f₃ : A → B} {f₄ : A → D} {f₅ f₆ : A → D}
  {H₁ : (x : A) → g₁ (f₂ x) == f₁ x} {H₂ : (x : A) → f₂ x == f₃ x}
  {H₃ : (x : A) → g₁ (f₃ x) == g₂ (f₄ x)}
  {H₄ : (x : A) → f₅ x == f₆ x} {H₅ : (x : A) → f₆ x == f₄ x}
  {x y : A} (p : x == y)
  {σ₁ : _} {σ₂ : _} {σ₃ : _} {σ₄ : _} {σ₅ : _}
  (e₁ : hmpty-nat-∙' H₁ p == ↯ σ₁) (e₂ : hmpty-nat-∙' H₂ p == ↯ σ₂)
  (e₃ : hmpty-nat-∙' H₃ p == ↯ σ₃) (e₄ : hmpty-nat-∙' H₄ p == ↯ σ₄) (e₅ : hmpty-nat-∙' H₅ p == ↯ σ₅) where

  open PFunc4 g₁ g₂ p e₁ e₂ e₃ e₄ e₅

  abstract
    hnat-∙'-!ap-!ap∙-=ₛ :
      hmpty-nat-∙' (λ x → ! (H₁ x) ∙ ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) p ◃∎
        =ₛ
      hnat-∙'̇-!-aux (ap f₁ p) (H₁ x) (H₁ y) ◃∙
      seq-! (ap-seq (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) σ₁) ∙∙
      ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∘ g₁ f₂ p) ◃∙
      ap-seq (λ q → ! (H₁ x) ∙ ap g₁ q ∙' ! (! (H₁ y))) σ₂ ∙∙
      ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∙-∙'! g₁ (H₂ x) (ap f₃ p) (H₂ y)) ◃∙
      ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) (∘-ap g₁ f₃ p)) ◃∙
      ap-seq ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))) σ₃ ∙∙
      ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘  (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘  (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (hnat-∙'̇-!-aux (ap (g₂ ∘ f₄) p) (ap g₂ (H₄ x ∙ H₅ x)) (ap g₂ (H₄ y ∙ H₅ y))) ◃∙
      ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (λ q → ap g₂ (H₄ x ∙ H₅ x) ∙ q ∙' ! (ap g₂ (H₄ y ∙ H₅ y))) (∘-ap g₂ f₄ p)))) ◃∙
      ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∙-∙'! g₂ (H₄ x ∙ H₅ x) (ap f₄ p) (H₄ y ∙ H₅ y)))) ◃∙
      ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (ap g₂) (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap f₄ p) (H₅ y) (H₄ y))))) ◃∙
      seq-! (ap-seq
          (((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) ∘
            (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) ∘ ap g₂ ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) σ₅) ∙∙
      seq-! (ap-seq
          (((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) ∘
            (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ ap g₂ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y))))) σ₄) ∙∙
      ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∘ g₂ f₅ p))) ◃∙
      ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
        (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))
          (hnat-∙'̇-∙-aux (H₃ x) (! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (! (ap g₂ (H₄ y ∙ H₅ y))) (H₃ y))) ◃∙
      ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
        (hnat-∙'̇-∙-aux (ap g₁ (H₂ x)) (H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (ap g₁ (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (H₁ x)) (ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (ap g₁ (H₂ y) ∙ H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (! (H₁ y)) ◃∎
    hnat-∙'-!ap-!ap∙-=ₛ = hnat-∙'-!ap-!ap∙-=ₛ0 ∙ₛ (hnat-∙'-!ap-!ap∙-=ₛ1 ∙ₛ (hnat-∙'-!ap-!ap∙-=ₛ2 ∙ₛ hnat-∙'-!ap-!ap∙-=ₛ3))
