{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.GrpMap-conv2
open import 2Grp
open import Hmtpy2Grp
open import Delooping
open import Bicategory
open import 2Grp-bc
open import Ptd-bc
open import Loop-PFunctor
open import K-PFunctor
open import SqLoopK
open import LoopK-ptr-idf
open import LoopK-ptr-comp

-- Pseudotransformation from identity to Ω ∘ K₂

module LoopK-PT {i} where
