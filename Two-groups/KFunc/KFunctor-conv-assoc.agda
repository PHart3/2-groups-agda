{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.PtdMap-conv
open import KFunctor
open import KFunctor-comp
open import apK
open import KFunctor-comp-assoc

module KFunctor-conv-assoc where

module _ {i j} {X : Ptd i} {Y : Ptd j} where

-- make all final conversions abstract
