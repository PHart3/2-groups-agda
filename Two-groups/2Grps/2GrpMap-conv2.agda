{-# OPTIONS --without-K --rewriting --overlapping-instances --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpMap
open import NatIso
open import 2GrpMap-conv
open import apK

-- more preservation properties of natiso2G-to-==

module 2GrpMap-conv2 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

-- make all final conversions abstract
