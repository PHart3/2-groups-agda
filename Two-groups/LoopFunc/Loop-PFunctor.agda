{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import Bicategory
open import Ptd-bc
open import 2Grp-bc
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import 2GrpMap-conv2

--  Ω as a pseudofunctor

module Loop-PFunctor {i} where
