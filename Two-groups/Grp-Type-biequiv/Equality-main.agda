{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import AdjEq
open import AdjEq-exmps
open import 2Grp-bc
open import Ptd-bc
open import Biadj-beqv
open import Biequiv-main

-- Final theorem: Ω produces an equality between 2-groups and pointed connected 2-types.

module Equality-main (i : ULevel) where

  2Grp-Ptd02-eql-Ω : (Ptd02 i , Ptd02-bicat i) == (2Grp-tot i , 2grp-bicat i)
  2Grp-Ptd02-eql-Ω = baequiv-to-==-R (2Grp-Ptd02-baeq i)
