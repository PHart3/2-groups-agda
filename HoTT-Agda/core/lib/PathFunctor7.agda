{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathFunctor2
open import lib.path-seq.Ap
open import lib.path-seq.Inversion
open import lib.path-seq.Concat
open import lib.path-seq.Reasoning

module lib.PathFunctor7 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (g : B → C)
  {f₁ f₂ : A → B} (H : (x : A) → f₁ x == f₂ x) {x y : A} (p : x == y) where

  abstract
    hnat-∙'-!ap :
      hmtpy-nat-∙' (λ x → ! (ap g (H x))) p ◃∎
        =ₛ
      hnat-∙'̇-!-aux (ap (g ∘ f₂) p) (ap g (H x)) (ap g (H y)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap (λ q → ap g (H x) ∙ q ∙' ! (ap g (H y))) (∘-ap g (λ z → f₂ z) p))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∙-∙'! g (H x) (ap (λ z → f₂ z) p) (H y))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ ap g q ∙' ! (! (ap g (H y)))) (hmtpy-nat-∙' H p)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∘ g f₁ p)) ◃∎
    hnat-∙'-!ap =
      hmtpy-nat-∙' (λ x → ! (ap g (H x))) p ◃∎
        =ₛ⟨ hnat-∙'-! (λ x → ap g (H x)) p ⟩
      hnat-∙'̇-!-aux (ap (g ∘ f₂) p) (ap g (H x)) (ap g (H y)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (hmtpy-nat-∙' (λ x₁ → ap g (H x₁)) p)) ◃∎
        =ₛ⟨ 1 & 1 & !-=ₛ (ap-seq-=ₛ (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (hnat-∙'-post H g p)) ⟩
      hnat-∙'̇-!-aux (ap (g ∘ f₂) p) (ap g (H x)) (ap g (H y)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap (λ q → ap g (H x) ∙ q ∙' ! (ap g (H y))) (∘-ap g (λ z → f₂ z) p))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∙-∙'! g (H x) (ap (λ z → f₂ z) p) (H y))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap (ap g) (hmtpy-nat-∙' H p))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∘ g f₁ p)) ◃∎
        =ₛ₁⟨ 3 & 1 & ap ! (∘-ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap g) (hmtpy-nat-∙' H p))  ⟩
      hnat-∙'̇-!-aux (ap (g ∘ f₂) p) (ap g (H x)) (ap g (H y)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap (λ q → ap g (H x) ∙ q ∙' ! (ap g (H y))) (∘-ap g (λ z → f₂ z) p))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∙-∙'! g (H x) (ap (λ z → f₂ z) p) (H y))) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ ap g q ∙' ! (! (ap g (H y)))) (hmtpy-nat-∙' H p)) ◃∙
      ! (ap (λ q → ! (ap g (H x)) ∙ q ∙' ! (! (ap g (H y)))) (ap-∘ g f₁ p)) ◃∎ ∎ₛ

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  (g₁ : B → C) (g₂ : A → D) {f₀ f₁ : A → B} {f₂ f₃ : A → C} {f₄ f₅ : D → C} 
  (H₁ : (x : A) → f₀ x == f₁ x) (H₂ : (x : A) → f₂ x == g₁ (f₀ x)) (H₃ : (x : A) →  f₂ x == f₃ x)
  (H₄ : (x : A) → f₃ x == f₄ (g₂ x)) (H₅ : (x : D) → f₄ x == f₅ x)
  {x y : A} (p : x == y) {σ₁ : _} {σ₂ : _} {σ₃ : _} {σ₄ : _} {σ₅ : _}
  (e₁ : hmtpy-nat-∙' H₁ p ◃∎ =ₛ σ₁) (e₂ : hmtpy-nat-∙' H₂ p ◃∎ =ₛ σ₂) (e₃ : hmtpy-nat-∙' H₃ p ◃∎ =ₛ σ₃)
  (e₄ : hmtpy-nat-∙' H₄ p ◃∎ =ₛ σ₄) (e₅ : hmtpy-nat-∙' H₅ (ap g₂ p) ◃∎ =ₛ σ₅) where

  private

    Θ =
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₁ p)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmtpy-nat-∙' H₅ (ap g₂ p)) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎

    τ₁ =
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z))) p ◃∙
        ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
        ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
        ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
        ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
        ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
          (hmtpy-nat-∙' (λ z → H₅ (g₂ z)) p) ◃∙
        ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
          (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
        ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
          (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
        ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
          (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
        hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎

    Δ =
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      seq-! (ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) σ₁) ∙∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      seq-! (ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₂) ∙∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₃ ∙∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ q ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₄ ∙∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ f₄ g₂ p) ◃∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₅ ∙∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎

    τ₂ =
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₁ p)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₃ ∙∙
      ap-seq ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) σ₄ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap-seq ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) σ₅ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎

  abstract
  
    hnat-∙'-!ap-∙!-∙∙-pre0 :
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z)) ∙ ! (H₂ z) ∙ H₃ z ∙ H₄ z ∙ H₅ (g₂ z)) p ◃∎
        =ₛ
      Θ
    hnat-∙'-!ap-∙!-∙∙-pre0 =
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z)) ∙ ! (H₂ z) ∙ H₃ z ∙ H₄ z ∙ H₅ (g₂ z)) p ◃∎
        =ₛ⟨ hnat-∙'-∙5 p (λ z → ! (ap g₁ (H₁ z))) (λ z → ! (H₂ z)) H₃ H₄ (λ z → H₅ (g₂ z)) ⟩
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z))) p ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' (λ z → ! (H₂ z)) p) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmtpy-nat-∙' (λ z → H₅ (g₂ z)) p) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'-! H₂ p) ⟩
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z))) p ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (! (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hmtpy-nat-∙' H₂ p))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmtpy-nat-∙' (λ z → H₅ (g₂ z)) p) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ₁⟨ 2 & 1 &
          ap-! (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hmtpy-nat-∙' H₂ p)) ∙
          ap ! (∘-ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hmtpy-nat-∙' H₂ p)) ⟩
      τ₁
        =ₛ⟨ 5 & 1 & 
          ap-seq-=ₛ
            ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
            (hnat-∙'-pre H₅ g₂ p) ⟩
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z))) p ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmtpy-nat-∙' H₅ (ap g₂ p)) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ⟨ 0 & 1 & hnat-∙'-!ap g₁ H₁ p ⟩
      Θ ∎ₛ

    hnat-∙'-!ap-∙!-∙∙-pre1 : Θ =ₛ Δ
    hnat-∙'-!ap-∙!-∙∙-pre1 =
      Θ
        =ₛ⟨ 10 & 1 & 
          ap-seq-=ₛ
            ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
            e₅ ⟩
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₁ p)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmtpy-nat-∙' H₄ p) ◃∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap-seq ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) σ₅ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ⟨ 8 & 1 & 
          ap-seq-=ₛ
            ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
            e₄ ⟩
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₁ p)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₃ p) ◃∙
      ap-seq ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) σ₄ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap-seq ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) σ₅ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ⟨ 7 & 1 & ap-seq-=ₛ (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) e₃ ⟩
      τ₂
        =ₛ⟨ 6 & 1 & !-=ₛ (ap-seq-=ₛ (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) e₂) ⟩
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) (hmtpy-nat-∙' H₁ p)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      seq-! (ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₂) ∙∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₃ ∙∙
      ap-seq ((λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) σ₄ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap-∘ f₄ g₂ p) ◃∙
      ap-seq ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) σ₅ ∙∙
      ap ((λ v → ! (ap g₁ (H₁ x)) ∙ v ∙' ! (! (ap g₁ (H₁ y)))) ∘ (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
        =ₛ⟨ 3 & 1 & !-=ₛ (ap-seq-=ₛ (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) e₁) ⟩
      Δ ∎ₛ

  abstract
    hnat-∙'-!ap-∙!-∙∙-pre :
      hmtpy-nat-∙' (λ z → ! (ap g₁ (H₁ z)) ∙ ! (H₂ z) ∙ H₃ z ∙ H₄ z ∙ H₅ (g₂ z)) p ◃∎
        =ₛ
      hnat-∙'̇-!-aux (ap (g₁ ∘ f₁) p) (ap g₁ (H₁ x)) (ap g₁ (H₁ y)) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap (λ q → ap g₁ (H₁ x) ∙ q ∙' ! (ap g₁ (H₁ y))) (∘-ap g₁ f₁ p))) ◃∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∙-∙'! g₁ (H₁ x) (ap f₁ p) (H₁ y))) ◃∙
      seq-! (ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ ap g₁ q ∙' ! (! (ap g₁ (H₁ y)))) σ₁) ∙∙
      ! (ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ g₁ f₀ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y)))) (hnat-∙'̇-!-aux (ap (g₁ ∘ f₀) p) (H₂ x) (H₂ y)) ◃∙
      seq-! (ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₂) ∙∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ q ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₃ ∙∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ q ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₄ ∙∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) (ap-∘ f₄ g₂ p) ◃∙
      ap-seq (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y)))) σ₅ ∙∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ (! (H₂ x) ∙ (H₃ x ∙ (H₄ x ∙ q ∙' ! (H₄ y)) ∙' ! (H₃ y)) ∙' ! (! (H₂ y))) ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → H₅ (g₂ x) ∙ q ∙' ! (H₅ (g₂ y))) (∘-ap (λ z → f₅ z) g₂ p)) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y)) (hnat-∙'̇-∙-aux (H₄ x) (H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₅ (g₂ y)) (H₄ y)))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (ap (λ q → ! (H₂ x) ∙ q ∙' ! (! (H₂ y))) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₄ y ∙ H₅ (g₂ y)) (H₃ y))) ◃∙
      ap (λ q → ! (ap g₁ (H₁ x)) ∙ q ∙' ! (! (ap g₁ (H₁ y))))
        (hnat-∙'̇-∙-aux (! (H₂ x)) (H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (H₂ y))) ◃∙
      hnat-∙'̇-∙-aux (! (ap g₁ (H₁ x))) (! (H₂ x) ∙ H₃ x ∙ H₄ x ∙ H₅ (g₂ x)) (ap (f₅ ∘ g₂) p) (! (H₂ y) ∙ H₃ y ∙ H₄ y ∙ H₅ (g₂ y)) (! (ap g₁ (H₁ y))) ◃∎
    hnat-∙'-!ap-∙!-∙∙-pre = hnat-∙'-!ap-∙!-∙∙-pre0 ∙ₛ hnat-∙'-!ap-∙!-∙∙-pre1
