{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.path-seq.Ap
open import lib.path-seq.Reasoning

module lib.PathFunctor2 where

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {x y : A} (p : x == y) where

    hnat-∙'-∙3 : {f₁ f₂ f₃ f₄ : A → B}
      (H₁ : (x : A) → f₁ x == f₂ x) (H₂ : (x : A) →  f₂ x == f₃ x) (H₃ : (x : A) → f₃ x == f₄ x)
      →
      hmpty-nat-∙' (λ x → H₁ x ∙ H₂ x ∙ H₃ x) p ◃∎
        =ₛ
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap (λ z → f₄ z) p) (H₃ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x) (ap (λ z → f₄ z) p) (H₂ y ∙ H₃ y) (H₁ y) ◃∎
    hnat-∙'-∙3 {f₄ = f₄} H₁ H₂ H₃ =
      hmpty-nat-∙' (λ x → H₁ x ∙ H₂ x ∙ H₃ x) p ◃∎
        =ₛ⟨ hnat-∙'-∙ H₁ (λ x → H₂ x ∙ H₃ x) p ⟩
      _
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'-∙ H₂ H₃ p) ⟩
      _
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hmpty-nat-∙' H₃ p) ⟩
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x) (ap (λ z → f₄ z) p) (H₃ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x) (ap (λ z → f₄ z) p) (H₂ y ∙ H₃ y) (H₁ y) ◃∎ ∎ₛ

    hnat-∙'-∙4 : {f₁ f₂ f₃ f₄ f₅ : A → B}
      (H₁ : (x : A) → f₁ x == f₂ x) (H₂ : (x : A) →  f₂ x == f₃ x) (H₃ : (x : A) → f₃ x == f₄ x)
      (H₄ : (x : A) → f₄ x == f₅ x)
      →
      hmpty-nat-∙' (λ x →  H₁ x ∙ H₂ x ∙ H₃ x ∙ H₄ x) p ◃∎
        =ₛ
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (hmpty-nat-∙' H₄ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x) (ap (λ z → f₅ z) p) (H₄ y) (H₃ y))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x ∙ H₄ x) (ap (λ z → f₅ z) p) (H₃ y ∙ H₄ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x ∙ H₄ x) (ap (λ z → f₅ z) p) (H₂ y ∙ H₃ y ∙ H₄ y) (H₁ y) ◃∎
    hnat-∙'-∙4 {f₅ = f₅} H₁ H₂ H₃ H₄ =
      hmpty-nat-∙' (λ x → H₁ x ∙ H₂ x ∙ H₃ x ∙ H₄ x) p ◃∎
        =ₛ⟨ hnat-∙'-∙ H₁ (λ x → H₂ x ∙ H₃ x ∙ H₄ x) p ⟩
      _
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'-∙3 H₂ H₃ H₄) ⟩
      _
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hmpty-nat-∙' H₃ p) ⟩
      _
        =ₛ₁⟨ 3 & 1 & 
          ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
            ((λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmpty-nat-∙' H₄ p) ⟩
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
        (hmpty-nat-∙' H₄ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x) (ap (λ z → f₅ z) p) (H₄ y) (H₃ y))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'̇-∙-aux (H₂ x) (H₃ x ∙ H₄ x) (ap (λ z → f₅ z) p) (H₃ y ∙ H₄ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x ∙ H₄ x) (ap (λ z → f₅ z) p) (H₂ y ∙ H₃ y ∙ H₄ y) (H₁ y) ◃∎ ∎ₛ

    hnat-∙'-∙5 : {f₁ f₂ f₃ f₄ f₅ f₆ : A → B}
      (H₁ : (x : A) → f₁ x == f₂ x) (H₂ : (x : A) →  f₂ x == f₃ x) (H₃ : (x : A) → f₃ x == f₄ x)
      (H₄ : (x : A) → f₄ x == f₅ x) (H₅ : (x : A) → f₅ x == f₆ x)
      →
      hmpty-nat-∙' (λ x →  H₁ x ∙ H₂ x ∙ H₃ x ∙ H₄ x ∙ H₅ x) p ◃∎
        =ₛ
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmpty-nat-∙' H₄ p) ◃∙
      ap
        ((λ v → H₁ x ∙ v ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘
          (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmpty-nat-∙' H₅ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y))
          (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y))
            (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap (λ z → f₆ z) p) (H₅ y) (H₄ y)))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₄ y ∙ H₅ y) (H₃ y))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (hnat-∙'̇-∙-aux (H₂ x) (H₃ x ∙ H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₃ y ∙ H₄ y ∙ H₅ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x ∙ H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₂ y ∙ H₃ y ∙ H₄ y ∙ H₅ y) (H₁ y) ◃∎
    hnat-∙'-∙5 {f₆ = f₆} H₁ H₂ H₃ H₄ H₅ =
      hmpty-nat-∙' (λ x →  H₁ x ∙ H₂ x ∙ H₃ x ∙ H₄ x ∙ H₅ x) p ◃∎
        =ₛ⟨ hnat-∙'-∙ H₁ (λ x → H₂ x ∙ H₃ x ∙ H₄ x ∙ H₅ x) p ⟩
      _
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hnat-∙'-∙4 H₂ H₃ H₄ H₅) ⟩
      _
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (λ q → H₂ x ∙ q ∙' ! (H₂ y)) _ ⟩
      _
        =ₛ₁⟨ 3 & 1 & ∘-ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) ((λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) _ ⟩
      _
        =ₛ₁⟨ 4 & 1 & ∘-ap _ ((λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) _ ⟩
      hmpty-nat-∙' H₁ p ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y)) (hmpty-nat-∙' H₂ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y))) (hmpty-nat-∙' H₃ p) ◃∙
      ap ((λ q → H₁ x ∙ q ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) (hmpty-nat-∙' H₄ p) ◃∙
      ap
        ((λ v → H₁ x ∙ v ∙' ! (H₁ y)) ∘ (λ q → H₂ x ∙ q ∙' ! (H₂ y)) ∘
          (λ q → H₃ x ∙ q ∙' ! (H₃ y)) ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmpty-nat-∙' H₅ p) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y))
          (ap (λ q → H₃ x ∙ q ∙' ! (H₃ y))
            (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap (λ z → f₆ z) p) (H₅ y) (H₄ y)))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (ap (λ q → H₂ x ∙ q ∙' ! (H₂ y)) (hnat-∙'̇-∙-aux (H₃ x) (H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₄ y ∙ H₅ y) (H₃ y))) ◃∙
      ap (λ q → H₁ x ∙ q ∙' ! (H₁ y))
        (hnat-∙'̇-∙-aux (H₂ x) (H₃ x ∙ H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₃ y ∙ H₄ y ∙ H₅ y) (H₂ y)) ◃∙
      hnat-∙'̇-∙-aux (H₁ x) (H₂ x ∙ H₃ x ∙ H₄ x ∙ H₅ x) (ap (λ z → f₆ z) p) (H₂ y ∙ H₃ y ∙ H₄ y ∙ H₅ y) (H₁ y) ◃∎ ∎ₛ
