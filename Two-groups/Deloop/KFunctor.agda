{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 #-}

open import lib.Basics
open import 2Magma
open import 2Grp

module KFunctor where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G