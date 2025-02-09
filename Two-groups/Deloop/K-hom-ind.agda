{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import lib.cubical.PathPathOver
open import 2Grp

-- induction principle for homotopy of functions out of K₂

module K-hom-ind where

-- tiny ad-hoc lemma for path algebra below

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ∙-assoc2-!-inv-l : {x : A} {y : B} (p₁ : y == f x) (p₂ p₃ : x == x)
    → (p₁ ∙ ap f p₂ ∙ ! p₁) ∙ p₁ ∙ ap f p₃ ∙ ! p₁ == p₁ ∙ ap f (p₂ ∙ p₃) ∙ ! p₁
  ∙-assoc2-!-inv-l idp p₂ p₃ =
    ap (λ q → q ∙ ap f p₃ ∙ idp) (∙-unit-r (ap f p₂)) ∙
    ! (∙-assoc (ap f p₂) (ap f p₃) idp) ∙
    ap (λ q → q ∙ idp) (∙-ap f p₂ p₃)

module _ {i j} {G : Type i} {{η : CohGrp G}} {X : Type j} {{_ : has-level 2 X}} where

  open import Delooping G
  
  open CohGrp {{...}}

  module _ (f g : K₂ η → X)
    (base∼ : f base == g base)
    (loop∼ : (x : G) → ap f (loop x) == base∼ ∙ ap g (loop x) ∙ ! base∼)
    (loop-comp∼ : (x y : G) → 
      ∙-ap f (loop x) (loop y) ∙
      ap (ap f) (loop-comp x y) ∙
      loop∼ (mu x y)
        ==
      ap2 _∙_ (loop∼ x) (loop∼ y) ∙
      ∙-assoc2-!-inv-l g base∼ (loop x) (loop y) ∙
      ap (λ p → base∼ ∙ ap g p ∙ ! base∼) (loop-comp x y)) where

    K₂-∼-ind : f ∼ g
    K₂-∼-ind =
      K₂-elim {P = λ x → f x == g x} base∼
      (λ x → hmpty-nat-po== f g (loop x) (loop∼  x))
      {!!}
      {!!}
