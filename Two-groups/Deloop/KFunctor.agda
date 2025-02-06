{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import 2Magma
open import 2Grp

-- action of K₂ on maps

module KFunctor where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  open import Delooping

  open CohGrpHom
  open WkMagHomStr
  
