{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation

module Hmtpy2Grp where

-- homotopy 2-groups

module _ {i} (X : Ptd i) where

  π² : ℕ → Ptd i
  π² n = ⊙Trunc 1 (⊙Ω^ n X)
