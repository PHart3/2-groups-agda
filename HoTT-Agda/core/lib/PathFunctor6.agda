{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathFunctor2
open import lib.path-seq.Ap
open import lib.path-seq.Concat
open import lib.path-seq.Reasoning

module lib.PathFunctor6 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (g : B → C)
  {f₀ : A → C} {f₁ f₂ f₃ : A → B} (H₁ : (x : A) → f₀ x == g (f₁ x)) (H₂ : (x : A) → f₁ x == f₂ x) (H₃ : (x : A) →  f₂ x == f₃ x)
  {x y : A} (p : x == y) {σ₁ : _} {σ₂ : _} {σ₃ : _}
  (e₁ : hmtpy-nat-∙' H₁ p ◃∎ =ₛ σ₁) (e₂ : hmtpy-nat-∙' H₂ p ◃∎ =ₛ σ₂) (e₃ : hmtpy-nat-∙' H₃ p ◃∎ =ₛ σ₃) where

  abstract
    hnat-∙'-∙-ap-∙ :
      hmtpy-nat-∙' (λ z → H₁ z ∙ ap g (H₂ z ∙ H₃ z)) p ◃∎
        =ₛ
      σ₁ ∙∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap-seq (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) σ₂ ∙∙
      ap-seq (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
    hnat-∙'-∙-ap-∙ =
      hmtpy-nat-∙' (λ z → H₁ z ∙ ap g (H₂ z ∙ H₃ z)) p ◃∎
        =ₛ⟨ hnat-∙'-∙ H₁ (λ z → ap g (H₂ z ∙ H₃ z)) p ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' (λ z → ap g (H₂ z ∙ H₃ z)) p) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'-post (λ z → H₂ z ∙ H₃ z) g p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (ap g) (hmtpy-nat-∙' (λ z → H₂ z ∙ H₃ z) p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap g) (hmtpy-nat-∙' (λ z → H₂ z ∙ H₃ z) p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hmtpy-nat-∙' (λ z → H₂ z ∙ H₃ z) p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'-∙ H₂ H₃ p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hmtpy-nat-∙' H₃ p)) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ₁⟨ 3 & 1 & ∘-ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hmtpy-nat-∙' H₃ p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hmtpy-nat-∙' H₃ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) e₃ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap-seq (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) e₂ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap-seq (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) σ₂ ∙∙
      ap-seq (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 0 & 1 & e₁ ⟩
      σ₁ ∙∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∘ g f₁ p) ◃∙
      ap-seq (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) σ₂ ∙∙
      ap-seq (λ q → H₁ x ∙ ap g (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ ap g q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap f₃ p) (H₃ y) (H₂ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap-∙-∙'! g (H₂ x ∙ H₃ x) (ap f₃ p) (H₂ y ∙ H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (ap (λ q → ap g (H₂ x ∙ H₃ x) ∙ q ∙' ! (ap g (H₂ y ∙ H₃ y))) (∘-ap g f₃ p)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (ap g (H₂ x ∙ H₃ x)) (ap (g ∘ f₃) p) (ap g (H₂ y ∙ H₃ y)) (H₁ y) ◃∎ ∎ₛ


module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (g : B → C)
  {f₀ f₁ : A → C} {f₂ f₃ : A → B} (H₁ : (x : A) → f₀ x == f₁ x) (H₂ : (x : A) → f₁ x == g (f₂ x)) (H₃ : (x : A) →  f₂ x == f₃ x)
  {x y : A} (p : x == y) {σ₁ : _} {σ₂ : _} {σ₃ : _}
  (e₁ : hmtpy-nat-∙' H₁ p ◃∎ =ₛ σ₁) (e₂ : hmtpy-nat-∙' H₂ p ◃∎ =ₛ σ₂) (e₃ : hmtpy-nat-∙' H₃ p ◃∎ =ₛ σ₃) where

  abstract
    hnat-∙'-∙-post :
      hmtpy-nat-∙' (λ z → H₁ z ∙ H₂ z ∙ ap g (H₃ z)) p ◃∎
        =ₛ
      σ₁ ∙∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
    hnat-∙'-∙-post =
      hmtpy-nat-∙' (λ z → H₁ z ∙ H₂ z ∙ ap g (H₃ z)) p ◃∎
        =ₛ⟨ hnat-∙'-∙3 p H₁ H₂ (λ z → ap g (H₃ z)) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hmtpy-nat-∙' (λ z → ap g (H₃ z)) p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hnat-∙'-post H₃ g p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (ap g) (hmtpy-nat-∙' H₃ p)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
        =ₛ₁⟨ 3 & 1 & ∘-ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap g) (hmtpy-nat-∙' H₃ p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hmtpy-nat-∙' H₃ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) e₃ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) e₂ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎
        =ₛ⟨ 0 & 1 & e₁ ⟩
      σ₁ ∙∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ g f₂ p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ ap g q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∙-∙'! g (H₃ x) (ap f₃ p) (H₃ y)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → ap g (H₃ x) ∙ q ∙' ! (ap g (H₃ y))) (∘-ap g f₃ p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (ap g (H₃ x)) (ap (g ∘ f₃) p) (ap g (H₃ y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ ap g (H₃ x)) (ap (g ∘ f₃) p) (H₂ y ∙ ap g (H₃ y)) (H₁ y) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (g : A → C)
  {f₀ f₁ : A → B} {f₂ f₃ : C → B} (H₁ : (x : A) → f₀ x == f₁ x) (H₂ : (x : A) → f₁ x == f₂ (g x)) (H₃ : (x : C) → f₂ x == f₃ x)
  {x y : A} (p : x == y) {σ₁ : _} {σ₂ : _} {σ₃ : _}
  (e₁ : hmtpy-nat-∙' H₁ p ◃∎ =ₛ σ₁) (e₂ : hmtpy-nat-∙' H₂ p ◃∎ =ₛ σ₂) (e₃ : hmtpy-nat-∙' H₃ (ap g p) ◃∎ =ₛ σ₃) where

  abstract
    hnat-∙'-∙-pre :
      hmtpy-nat-∙' (λ z → H₁ z ∙ H₂ z ∙ H₃ (g z)) p ◃∎
        =ₛ
      σ₁ ∙∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ f₂ g p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → H₃ (g x) ∙ q ∙' ! (H₃ (g y))) (∘-ap f₃ g p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎
    hnat-∙'-∙-pre =
      hmtpy-nat-∙' (λ z → H₁ z ∙ H₂ z ∙ H₃ (g z)) p ◃∎
        =ₛ⟨ hnat-∙'-∙3 p H₁ H₂ (λ z → H₃ (g z)) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hmtpy-nat-∙' (λ z → H₃ (g z)) p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hnat-∙'-pre H₃ g p) ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ f₂ g p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (hmtpy-nat-∙' H₃ (ap g p)) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → H₃ (g x) ∙ q ∙' ! (H₃ (g y))) (∘-ap f₃ g p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) e₃ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmtpy-nat-∙' H₂ p) ◃∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ f₂ g p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → H₃ (g x) ∙ q ∙' ! (H₃ (g y))) (∘-ap f₃ g p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) e₂ ⟩
      hmtpy-nat-∙' H₁ p ◃∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ f₂ g p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → H₃ (g x) ∙ q ∙' ! (H₃ (g y))) (∘-ap f₃ g p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎
        =ₛ⟨ 0 & 1 & e₁ ⟩
      σ₁ ∙∙
      ap-seq (λ q → H₁ x ∙ q ∙' ! (H₁ y)) σ₂ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap-∘ f₂ g p) ◃∙
      ap-seq (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) σ₃ ∙∙
      ap (λ q → H₁ x ∙ (H₂ x ∙ q ∙' ! (H₂ y)) ∙' ! (H₁ y)) (ap (λ q → H₃ (g x) ∙ q ∙' ! (H₃ (g y))) (∘-ap f₃ g p)) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ (g x)) (ap (f₃ ∘ g) p) (H₃ (g y)) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ (g x)) (ap (f₃ ∘ g) p) (H₂ y ∙ H₃ (g y)) (H₁ y) ◃∎ ∎ₛ
