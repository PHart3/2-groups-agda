{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverId
open import 2Grp

-- induction principle for homotopy of functions out of K₂

module K-hom-ind where

module _ {i j} {G : Type i} {{η : CohGrp G}} {X : Type j} {{_ : has-level 2 X}} where

  open import Delooping G
  
  open CohGrp {{...}}

  module _ (f g : K₂ η → X)
    (base∼ : f base == g base)
    (loop∼ : (x : G) → ap f (loop x) == base∼ ∙ ap g (loop x) ∙' ! base∼)
    (loop-comp∼ : (x y : G) → 
      ∙-ap f (loop x) (loop y) ◃∙
      ap (ap f) (loop-comp x y) ◃∙
      loop∼ (mu x y) ◃∎
        =ₛ
      ap2 _∙_ (loop∼ x) (loop∼ y) ◃∙
      ∙-assoc2-!-inv-l g base∼ base∼ (loop x) (loop y) ◃∙
      ap (λ p → base∼ ∙ ap g p ∙' ! base∼) (loop-comp x y) ◃∎) where

    K₂-∼-ind : f ∼ g
    K₂-∼-ind =
      K₂-elim {P = λ x → f x == g x} base∼
      (λ x → from-hmpty-nat f g (loop x) (loop∼  x))
      (λ x y → PPOver-from-hnat f g (loop x) (loop y) (loop-comp x y) (loop∼ x) (loop∼ y) (loop∼ (mu x y)) (=ₛ-out (loop-comp∼ x y)))
      λ x y z → PPPOver-1type (loop-assoc x y z) _ _

    abstract
      K₂-∼-ind-β : (x : G) → hmpty-nat-∙' K₂-∼-ind (loop x) == loop∼ x
      K₂-∼-ind-β x =
        apd-to-hnat f g K₂-∼-ind (loop x) (loop∼ x)
        (loop-β
          base∼
          (λ x → from-hmpty-nat f g (loop x) (loop∼  x))
          (λ x y → PPOver-from-hnat f g (loop x) (loop y) (loop-comp x y) (loop∼ x) (loop∼ y) (loop∼ (mu x y)) (=ₛ-out (loop-comp∼ x y)))
          (λ x y z → PPPOver-1type (loop-assoc x y z) _ _)
        x)
