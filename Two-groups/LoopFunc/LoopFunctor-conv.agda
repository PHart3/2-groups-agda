{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import NatIso
open import 2GrpMap-conv
open import LoopFunctor

module LoopFunctor-conv where

open CohGrp {{...}}

module _ {ℓ₁ ℓ₂} {X₁ : Ptd ℓ₁} {X₂ : Ptd ℓ₂} {{η₁ : has-level 2 (de⊙ X₁)}} {{η₂ : has-level 2 (de⊙ X₂)}} where
