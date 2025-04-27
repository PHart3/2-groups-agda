{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEq

-- univalent (2,1)-categories

module Bicat-univ where

open BicatStr

module _ {i j} {B₀ : Type i} (ξB : BicatStr j B₀) where

  idtoiso-global : {a b : B₀} → a == b → AdjEquiv ξB a b
  idtoiso-global idp = {!!}

  is-univ-bc :  Type (lmax i j)
  is-univ-bc = (a b : B₀) → is-equiv (idtoiso-global {a} {b})
