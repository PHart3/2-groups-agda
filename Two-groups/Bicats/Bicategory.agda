{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

-- Warning: We define a bicategory as a (2,1)-category with paths as 2-cells.

module Bicategory where

module _ {i} (B₀ : Type i) where

  record BicatStr {j k} : Type (lmax i (lmax (lsucc j) (lsucc k))) where
    infixr 82 _·_
    field
      B₁ : B₀ → B₀ → Type j
      {{B₁-trunc}} : {a b : B₀} → has-level 1 (B₁ a b)
      id₁ : (a : B₀) → B₁ a a
      _·_ : {a b c : B₀} → B₁ a b → B₁ b c → B₁ a c
      lamb : {a b : B₀} (f : B₁ a b) → id₁ a · f == f
      ρ : {a b : B₀} (f : B₁ a b) → f · id₁ b == f
      α : {a b c d : B₀} (f : B₁ a b) (g : B₁ b c) (h : B₁ c d) → f · g · h == (f · g) · h
      -- 16-20 , 25-6 
