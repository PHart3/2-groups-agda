{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.types.PtdMap-conv2
open import 2Grp
open import Delooping
open import Bicategory
open import Ptd-bc
open import 2Grp-bc
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import KFunctor-comp-runit
open import KFunctor-comp-lunit
open import KFunctor-comp-assoc

-- K₂ as a pseudofunctor

module K-PFunctor {i : ULevel} where

open CohGrp {{...}}
