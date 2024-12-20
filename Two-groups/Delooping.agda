{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import 2Grp

-- delooping of a coherent 2-group via an EM-like HIT

module Delooping where

postulate -- HIT
  K₂ : ∀ {i} (G : Type i) → CohGrp {X = G} → Type i

module _ {i} {G : Type i} {η : CohGrp {X = G}} where

  open CohGrp {X = G}

  postulate -- HIT
    base : K₂ G η
    instance K₂-is-2type : has-level 2 (K₂ G η)

    -- 2-group morphism from G to Ω K₂
    loop : G → base == base
