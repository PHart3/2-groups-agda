{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv2
open import 2Grp
open import Hmtpy2Grp
open import Delooping
open import LoopK-hom
open import Bicategory
open import 2Grp-bc
open import Ptd-bc
open import Loop-PFunctor
open import K-PFunctor
open import SqKLoop
open import KLoop-ptr-idf
open import KLoop-ptr-comp

-- Pseudotransformation from K₂ ∘ Ω to identity

module KLoop-PT {i : ULevel} where
