{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import 2GrpHom2
open import 2GrpHom5

module 2GrpHomEq where

open CohGrp {{...}}

-- equivalence between full and short definition of 2-group morphism

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (map : G₁ → G₂) where
