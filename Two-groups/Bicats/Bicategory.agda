{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics

-- Warning: We define a bicategory as a (2,1)-category with paths as 2-cells.

module Bicategory where

module _ {i} (B₀ : Type i) where

  record bicat {j k} : Type (lmax i (lmax (lsucc j) (lsucc k))) where
    field
      B₁ : B₀ → B₀ → Type j
      B₂ : {a b : B₀} (f g : B₁ a b) → Type k
