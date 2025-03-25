{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import Decode-main
open import 2Grp-bc
open import Biequiv
open import AdjEq-exmps

module LoopK-adjeq where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  abstract
    Loop-adjeq-str : Adjequiv loop
    Loop-adjeq-str = 2g≃-to-adjeq loop-2g≃
