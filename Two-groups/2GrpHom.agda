{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp

module 2GrpHom where

open CohGrp {{...}}
open CohGrpHom

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  (φ : CohGrpHom {{η₁}} {{η₂}}) where
{-
  -- extracted map-id proof
  get-map-id : id == map φ id
  get-map-id = {!id == mu id id == mu (map φ id) (map φ id) == map φ (mu id id) == map φ id!}

  -- extracted map-inv proof
  get-map-comp : (x y : G₁) → mu (map φ x) (map φ y) == map φ (mu x y)
  get-map-comp x y = {!!}
-}
  -- equivalence between the two definitions of 2-group morphism
