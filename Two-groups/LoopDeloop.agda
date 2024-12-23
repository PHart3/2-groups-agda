{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.cubical.PathPathOver
open import 2Grp

module LoopDeloop where

module _ {i} (G : Type i) {η : CohGrp {X = G}} where

  open import Delooping G

  open CohGrp η

  Codes : K₂ η → 1 -Type i
  Codes = K₂-rec (G , 1trunc) {!!} {!!} {!!}
