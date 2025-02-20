{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.cubical.PathPathOver
open import 2Grp

module K-hom2-ind where

module _ {i j} {G : Type i} {{η : CohGrp G}} {X : Type j} {{_ : has-level 2 X}} where

  open import Delooping G
  
  open CohGrp {{...}}

  module _
    {f g : K₂ η → X}
    {H₁ H₂ : f ∼ g}
    (base∼∼ : H₁ base == H₂ base)
    (loop∼∼ : (x : G) →
      hmpty-nat-∙' H₁ (loop x)
        ==
      hmpty-nat-∙' H₂ (loop x) ∙' ap2 (λ p₁ p₂ → p₁ ∙ ap g (loop x) ∙' ! p₂) (! base∼∼) (! base∼∼))
    where

    K₂-∼-ind : H₁ ∼ H₂
    K₂-∼-ind =
      K₂-elim {P = λ x → H₁ x == H₂ x} base∼∼
      (λ x → from-hmpty-nat-d H₁ H₂ (loop x) (loop∼∼ x))
      (λ x y → PPOver-0type _ _)
      λ x y z → PPPOver-1type (loop-assoc x y z) _ _
