{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import lib.types.Paths
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverId
open import 2Grp

-- induction principle for homotopy of functions out of K₂

module K-hom-ind where

module _ {i j} {A : Type i} {B : Type j} {f g : A → B} (K : (z : A) → f z == g z) where

  apd-to-hnat-po== : {x y : A} (p : x == y) (m : ap f p == K x ∙ ap g p  ∙ ! (K y))
    → apd K p == hmpty-nat-po== f g p m → hmpty-nat-∙ K p == m
  apd-to-hnat-po== {x} idp m e = lemma (K x) m e
    where
      lemma : {x₁ x₂ : B} (v : x₁ == x₂) (n : idp == v ∙ ! v)
        (r : idp == ! (ap (λ p → p ∙ v) n ∙ ∙-assoc v (! v) v ∙ ap (_∙_ v) (!-inv-l v) ∙ ∙-unit-r v))
        → ! (!-inv-r v) == n
      lemma {x₁} idp n r = ! (ap-equiv-idp (post∙-is-equiv idp) aux)
        where
          aux : ap (λ p → p ∙ idp) n == idp
          aux = ! (!-! (ap (λ p → p ∙ idp) n)) ∙ ap ! (ap ! (! (∙-unit-r (ap (λ p → p ∙ idp) n)))) ∙ ap ! (! r)

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
      ∙-assoc2-!-inv-l g base∼ base∼ (loop x) (loop y) ∙
      ap (λ p → base∼ ∙ ap g p ∙ ! base∼) (loop-comp x y)) where

    K₂-∼-ind : f ∼ g
    K₂-∼-ind =
      K₂-elim {P = λ x → f x == g x} base∼
      (λ x → hmpty-nat-po== f g (loop x) (loop∼  x))
      (λ x y → PPOver-from-hnat f g (loop x) (loop y) (loop-comp x y) (loop∼ x) (loop∼ y) (loop∼ (mu x y)) (loop-comp∼ x y))
      λ x y z → PPPOver-1type (loop-assoc x y z) _ _

    K₂-∼-ind-β : (x : G) → hmpty-nat-∙ K₂-∼-ind (loop x) == loop∼ x
    K₂-∼-ind-β x =
      apd-to-hnat-po== K₂-∼-ind (loop x) (loop∼ x)
      (loop-β
        base∼
        (λ x → hmpty-nat-po== f g (loop x) (loop∼  x))
        (λ x y → PPOver-from-hnat f g (loop x) (loop y) (loop-comp x y) (loop∼ x) (loop∼ y) (loop∼ (mu x y)) (loop-comp∼ x y))
        (λ x y z → PPPOver-1type (loop-assoc x y z) _ _)
      x)
