{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import Bicategory

-- the bicategory of 1-types in a universe

module 1type-bc where

module _ (i : ULevel) where

  open BicatStr

  1type-bicat : BicatStr i (1 -Type i)
  hom 1type-bicat (X , _) (Y , _) = X → Y
  id₁ 1type-bicat _ = idf _
  _◻_ 1type-bicat g f = g ∘ f
  ρ 1type-bicat _ = idp
  lamb 1type-bicat _ = idp
  α 1type-bicat _ _ _ = idp
  tri-bc 1type-bicat _ _ = idp
  pent-bc 1type-bicat _ _ _ _ = idp
  hom-trunc 1type-bicat {b = (_ , tY)} = Π-level-instance {{tY}} 
