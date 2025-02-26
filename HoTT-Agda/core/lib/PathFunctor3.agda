{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathFunctor2
open import lib.path-seq.Ap
open import lib.path-seq.Inversion
open import lib.path-seq.Reasoning

module lib.PathFunctor3 where

module PFunc3 {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (g₁ : B → C) (g₂ : D → C)
  {f₁ : A → C} {f₂ f₃ : A → B} {f₄ : A → D} {f₅ f₆ : A → D}
  (H₁ : (x : A) → g₁ (f₂ x) == f₁ x) (H₂ : (x : A) → f₂ x == f₃ x)
  (H₃ : (x : A) → g₁ (f₃ x) == g₂ (f₄ x))
  (H₄ : (x : A) → f₅ x == f₆ x) (H₅ : (x : A) → f₆ x == f₄ x)
  {x y : A} (p : x == y) where

  𝕤 =
    hnat-∙'̇-!-aux (ap f₁ p) (H₁ x) (H₁ y) ◃∙
    ! (ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (hmpty-nat-∙' H₁ p)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∘ g₁ f₂ p) ◃∙
    ap (λ q → ! (H₁ x) ∙ ap g₁ q ∙' ! (! (H₁ y))) (hmpty-nat-∙' H₂ p) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∙-∙'! g₁ (H₂ x) (ap f₃ p) (H₂ y)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) (∘-ap g₁ f₃ p)) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))) (hmpty-nat-∙' H₃ p) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘  (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘  (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (hnat-∙'̇-!-aux (ap (g₂ ∘ f₄) p) (ap g₂ (H₄ x ∙ H₅ x)) (ap g₂ (H₄ y ∙ H₅ y))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (λ q → ap g₂ (H₄ x ∙ H₅ x) ∙ q ∙' ! (ap g₂ (H₄ y ∙ H₅ y)))
        (∘-ap g₂ f₄ p)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∙-∙'! g₂ (H₄ x ∙ H₅ x) (ap f₄ p) (H₄ y ∙ H₅ y)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (ap g₂) (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap f₄ p) (H₅ y) (H₄ y))))) ◃∙
    ! (ap
        (((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) ∘
          (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) ∘ ap g₂ ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
        (hmpty-nat-∙' H₅ p)) ◃∙
    ! (ap
        (((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y))) ∘
          (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ ap g₂ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))))
        (hmpty-nat-∙' H₄ p)) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∘ g₂ f₅ p))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))
        (hnat-∙'̇-∙-aux (H₃ x) (! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (! (ap g₂ (H₄ y ∙ H₅ y))) (H₃ y))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (hnat-∙'̇-∙-aux (ap g₁ (H₂ x)) (H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (ap g₁ (H₂ y))) ◃∙
    hnat-∙'̇-∙-aux (! (H₁ x)) (ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (ap g₁ (H₂ y) ∙ H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (! (H₁ y)) ◃∎

  hnat-∙'-!ap-!ap∙ :
    hmpty-nat-∙' (λ x → ! (H₁ x) ∙ ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) p ◃∎
      =ₛ
    𝕤
  hnat-∙'-!ap-!ap∙ = 
    hmpty-nat-∙' (λ x → ! (H₁ x) ∙ ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) p ◃∎
      =ₛ⟨ hnat-∙'-∙4 p (λ x → ! (H₁ x)) (λ x → ap g₁ (H₂ x)) H₃ (λ x → ! (ap g₂ (H₄ x ∙ H₅ x))) ⟩
    _
      =ₛ⟨ 3 & 1 & 
        ap-seq-=ₛ
          ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
          (hnat-∙'-!ap∙ g₂ H₄ H₅ p)
         ⟩
    _
      =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (hnat-∙'-post H₂ g₁ p) ⟩
    _
      =ₛ⟨ 0 & 1 & hnat-∙'-! H₁ p ⟩
    hnat-∙'̇-!-aux (ap f₁ p) (H₁ x) (H₁ y) ◃∙
    ! (ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (hmpty-nat-∙' H₁ p)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∘ g₁ f₂ p) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap (ap g₁) (hmpty-nat-∙' H₂ p)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∙-∙'! g₁ (H₂ x) (ap f₃ p) (H₂ y)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) (∘-ap g₁ f₃ p)) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))) (hmpty-nat-∙' H₃ p) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘  (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘  (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (hnat-∙'̇-!-aux (ap (g₂ ∘ f₄) p) (ap g₂ (H₄ x ∙ H₅ x)) (ap g₂ (H₄ y ∙ H₅ y))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (λ q → ap g₂ (H₄ x ∙ H₅ x) ∙ q ∙' ! (ap g₂ (H₄ y ∙ H₅ y)))
        (∘-ap g₂ f₄ p)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∙-∙'! g₂ (H₄ x ∙ H₅ x) (ap f₄ p) (H₄ y ∙ H₅ y)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (ap g₂) (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap f₄ p) (H₅ y) (H₄ y))))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap ((λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) ∘ ap g₂ ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) (hmpty-nat-∙' H₅ p))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ ap g₂ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (hmpty-nat-∙' H₄ p))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∘ g₂ f₅ p))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))
        (hnat-∙'̇-∙-aux (H₃ x) (! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (! (ap g₂ (H₄ y ∙ H₅ y))) (H₃ y))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (hnat-∙'̇-∙-aux (ap g₁ (H₂ x)) (H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (ap g₁ (H₂ y))) ◃∙
    hnat-∙'̇-∙-aux (! (H₁ x)) (ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (ap g₁ (H₂ y) ∙ H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (! (H₁ y)) ◃∎
      =ₛ₁⟨ 3 & 1 & ∘-ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap g₁) (hmpty-nat-∙' H₂ p) ⟩
    hnat-∙'̇-!-aux (ap f₁ p) (H₁ x) (H₁ y) ◃∙
    ! (ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (hmpty-nat-∙' H₁ p)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∘ g₁ f₂ p) ◃∙
    ap (λ q → ! (H₁ x) ∙ ap g₁ q ∙' ! (! (H₁ y))) (hmpty-nat-∙' H₂ p) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap-∙-∙'! g₁ (H₂ x) (ap f₃ p) (H₂ y)) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) (∘-ap g₁ f₃ p)) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))) (hmpty-nat-∙' H₃ p) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘  (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘  (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (hnat-∙'̇-!-aux (ap (g₂ ∘ f₄) p) (ap g₂ (H₄ x ∙ H₅ x)) (ap g₂ (H₄ y ∙ H₅ y))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (λ q → ap g₂ (H₄ x ∙ H₅ x) ∙ q ∙' ! (ap g₂ (H₄ y ∙ H₅ y)))
        (∘-ap g₂ f₄ p)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∙-∙'! g₂ (H₄ x ∙ H₅ x) (ap f₄ p) (H₄ y ∙ H₅ y)))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap (ap g₂) (hnat-∙'̇-∙-aux (H₄ x) (H₅ x) (ap f₄ p) (H₅ y) (H₄ y))))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap ((λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) ∘ ap g₂ ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y))) (hmpty-nat-∙' H₅ p))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ ap g₂ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (hmpty-nat-∙' H₄ p))) ◃∙
    ap ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
      (! (ap (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) (ap-∘ g₂ f₅ p))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (ap (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y)))
        (hnat-∙'̇-∙-aux (H₃ x) (! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (! (ap g₂ (H₄ y ∙ H₅ y))) (H₃ y))) ◃∙
    ap (λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y)))
      (hnat-∙'̇-∙-aux (ap g₁ (H₂ x)) (H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (ap g₁ (H₂ y))) ◃∙
    hnat-∙'̇-∙-aux (! (H₁ x)) (ap g₁ (H₂ x) ∙ H₃ x ∙ ! (ap g₂ (H₄ x ∙ H₅ x))) (ap (g₂ ∘ f₅) p) (ap g₁ (H₂ y) ∙ H₃ y ∙ ! (ap g₂ (H₄ y ∙ H₅ y))) (! (H₁ y)) ◃∎
      =ₛ₁⟨ 11 & 1 &
        !-∘-ap
          ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
          ((λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y)))) ∘ ap g₂ ∘ (λ q → H₄ x ∙ q ∙' ! (H₄ y)))
          (hmpty-nat-∙' H₅ p) ⟩
    _
      =ₛ₁⟨ 12 & 1 &
        !-∘-ap
          ((λ q → ! (H₁ x) ∙ q ∙' ! (! (H₁ y))) ∘ (λ q → ap g₁ (H₂ x) ∙ q ∙' ! (ap g₁ (H₂ y))) ∘ (λ q → H₃ x ∙ q ∙' ! (H₃ y)))
          (λ q → ! (ap g₂ (H₄ x ∙ H₅ x)) ∙ ap g₂ q ∙' ! (! (ap g₂ (H₄ y ∙ H₅ y))))
          (hmpty-nat-∙' H₄ p) ⟩
    𝕤 ∎ₛ
