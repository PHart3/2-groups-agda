{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.NType2
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Truncation

module lib.Function2 where

is-surj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-surj {A = A} f = ∀ b → Trunc -1 (hfiber f b)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C} where
  abstract
    ∘-is-surj : is-surj g → is-surj f → is-surj (g ∘ f)
    ∘-is-surj g-is-surj f-is-surj c =
      Trunc-rec
        (λ{(b , gb=c) →
          Trunc-rec
          (λ{(a , fa=b) → [ a , ap g fa=b ∙ gb=c ]})
          (f-is-surj b)})
        (g-is-surj c)

module _ {i j} {A : Type i} {B : Type j} where

  abstract
    equiv-is-surj : {f : A → B} → is-equiv f → is-surj f
    equiv-is-surj f-is-equiv b = [ g b , f-g b ]
      where open is-equiv f-is-equiv

  surj-emb-is-equiv-aux : {f : A → B} (y : B)
    → is-embedding f → Trunc -1 (hfiber f y) → is-contr (hfiber f y)
  surj-emb-is-equiv-aux {f} y e = Trunc-rec (λ t → has-level-in (t ,
    all-paths-fib t))
    where
      all-paths-fib : (p₁ p₂ : hfiber f y) → p₁ == p₂
      all-paths-fib (x , p) (y , q) =
        pair= (is-equiv.g (e x y) (p ∙' ! q))
          (↓-app=cst-in'-rot (is-equiv.f-g (e x y) ( p ∙' ! q) ))

  abstract
    surj-emb-is-equiv : {f : A → B} → (is-embedding f × is-surj f) → is-equiv f
    surj-emb-is-equiv {f} (e , s) = contr-map-is-equiv λ y → surj-emb-is-equiv-aux y e (s y)
