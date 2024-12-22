{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.cubical.PathPathOver
open import 2Grp

-- delooping of a coherent 2-group via an EM-like 3-HIT

module Delooping {i} (G : Type i) where

postulate -- HIT
  K₂ : CohGrp {X = G} → Type i

module _ {η : CohGrp {X = G}} where

  open CohGrp {X = G} η

  postulate -- HIT
    base : K₂ η
    instance K₂-is-2type : has-level 2 (K₂ η)

    -- 2-group morphism from G to Ω K₂
    -- Preservation of inverse and unit come for free.
    loop : G → base == base
    loop-comp : (x y : G) → loop x ∙ loop y == loop (mu x y)
    loop-assoc : (x y z : G) →
      ∙-assoc (loop x) (loop y) (loop z) ∙
      ap (λ p → loop x ∙ p) (loop-comp y z) ∙
      loop-comp x (mu y z)
        ==
      ap (λ p → p ∙ loop z) (loop-comp x y) ∙
      loop-comp (mu x y) z ∙
      ! (ap loop (al x y z))

  module K₂Elim {j} {P : K₂ η → Type j}
    {{p : {x : K₂ η} → has-level 2 (P x)}}
    (base* : P base)
    (loop* : (x : G) → base* == base* [ P ↓ loop x ])
    (loop-comp* : (x y : G) →
      PPOver (loop-comp x y) (loop* x ∙ᵈ loop* y) (loop* (mu x y)))
    (loop-assoc* : (x y z : G) →
      PPPOver (loop-assoc x y z)
        (∙ᵈ-assoc-ppo (loop* x) (loop* y) (loop* z) ∙ᶜ
        ap-∙-preᶜ (loop* x) (loop-comp* y z) ∙ᶜ
        loop-comp* x (mu y z))
        (ap-∙-postᶜ (loop* z) (loop-comp* x y) ∙ᶜ
        loop-comp* (mu x y) z ∙ᶜ
        !ᶜ (apd-po loop* (al x y z))))
    where

    postulate -- HIT
      f : Π (K₂ η) P
      base-β : f base ↦ base*
    {-# REWRITE base-β #-}

    postulate -- HIT
      loop-β : (x : G) → apd f (loop x) == loop* x
      loop-comp-β : (x y : G) →
        apdd-∙ᵈ f (loop x) (loop y) (loop-comp x y)
        ==
        apᶜ² (! (loop-β x) ∙ᵈ= ! (loop-β y)) (! (loop-β (mu x y))) (loop-comp* x y)

  open K₂Elim public using () renaming (f to K₂-elim)

  module K₂Rec {j} {B : Type j} {{_ : has-level 2 B}}
    (base* : B) (loop* : G → base* == base*)
    (loop-comp* : (x y : G) → loop* x ∙ loop* y == loop* (mu x y))
    (loop-assoc* : (x y z : G) → 
      ∙-assoc (loop* x) (loop* y) (loop* z) ∙
      ap (λ p → loop* x ∙ p) (loop-comp* y z) ∙
      loop-comp* x (mu y z)
        ==
      ap (λ p → p ∙ loop* z) (loop-comp* x y) ∙
      loop-comp* (mu x y) z ∙
      ! (ap loop* (al x y z)))
    where

    private
      module M =
        K₂Elim
          base*
          (λ x → ↓-cst-in (loop* x))
          (λ x y → ppo-cst-in-∙ {p₁ = loop x} (loop-comp x y) (loop-comp* x y))
          (λ x y z → {!!})

    f : K₂ η → B
    f = M.f

    -- β rules

  open K₂Rec public using () renaming (f to K₂Rec)
