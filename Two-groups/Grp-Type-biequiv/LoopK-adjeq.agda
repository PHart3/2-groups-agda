{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Delooping-equiv
open import 2Grp-bc
open import AdjEq
open import AdjEq-exmps

module LoopK-adjeq where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  abstract
    Loop-adjeq-str : Adjequiv (K₂-loopmap)
    Loop-adjeq-str = 2g≃-to-adjeq loop-2g≃
