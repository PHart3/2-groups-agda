{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.PtdMap-conv

module KFunctor-conv where

module _ {i j} {X : Ptd i} {Y : Ptd j} where

-- make all final conversions abstract
