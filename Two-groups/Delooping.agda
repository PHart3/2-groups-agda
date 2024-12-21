{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.cubical.PathPathOver
open import 2Grp

-- delooping of a coherent 2-group via an EM-like 3-HIT

module Delooping where

postulate -- HIT
  K₂ : ∀ {i} (G : Type i) → CohGrp {X = G} → Type i

module _ {i} {G : Type i} {η : CohGrp {X = G}} where

  open CohGrp {X = G} η

  postulate -- HIT
    base : K₂ G η
    instance K₂-is-2type : has-level 2 (K₂ G η)

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

  module K₂Elim {j} {P : K₂ G η → Type j}
    {{p : {x : K₂ G η} → has-level 2 (P x)}}
    (base* : P base)
    (loop* : (x : G) → base* == base* [ P ↓ loop x ])
    (loop-comp* : (x y : G) →
      PathPathOver (loop-comp x y) (loop* x ∙ᵈ loop* y) (loop* (mu x y)))
    -- 3-dim pathover
    where
