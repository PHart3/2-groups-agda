{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import Bicategory
open import 2Grp-bc
open import Ptd-bc
open import Loop-PFunctor
open import K-PFunctor
open import LoopK-PT
open import KLoop-PT
open import KLoop-adjeq
open import LoopK-adjeq

-- Final theorem: biequivalence between 2-groups and pointed connected 2-types

module Biequiv-main {i} where
