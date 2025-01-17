{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Truncation
open import lib.cubical.PathPathOver
open import 2Magma
open import 2Grp
open import 2GrpAutoEq
open import Hmtpy2Grp

module LoopDeloop where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp η

  open import Delooping G

  Codes : K₂ η → 1 -Type i
  Codes =
    K₂-rec (G , 1trunc)
      (loop' (2Grp-1Ty-lmap {{η}}))
      (loop-comp' (2Grp-1Ty-lmap {{η}}))
      (loop-assoc' (2Grp-1Ty-lmap {{η}}))
