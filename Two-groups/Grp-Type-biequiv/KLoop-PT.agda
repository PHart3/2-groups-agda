{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.PtdMap-conv
open import 2Grp
open import Hmtpy2Grp
open import Delooping
open import KFunctor
open import SqKLoop
open import KLoop-ptr-idf
open import KLoop-ptr-comp

-- Pseudotransformation from K₂ ∘ Ω to identity

module KLoop-PT {i : ULevel} where
