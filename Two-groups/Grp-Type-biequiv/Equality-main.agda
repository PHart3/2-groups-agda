{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import AdjEq
open import AdjEq-exmps
open import 2Grp
open import 2Grp-bc
open import Ptd-bc
open import Biequiv
open import Biequiv-main

-- Final theorem: two equalities between 2-groups and pointed connected 2-types, one from Ω and one from K₂

module Equality-main (i : ULevel) where

  -- equality induced by Ω
  2Grp-Ptd02-eql-Ω : (Ptd02 i , Ptd02-bicat i) == (2Grp-tot i , 2grp-bicat i)
  2Grp-Ptd02-eql-Ω = baequiv-to-==-R univ-Pt02 univ-2G (2Grp-Ptd02-baeq i)
  
  -- equality induced by K₂
  2Grp-Ptd02-eql-K₂ : (2Grp-tot i , 2grp-bicat i) == (Ptd02 i , Ptd02-bicat i)
  2Grp-Ptd02-eql-K₂ = baequiv-to-==-L univ-2G univ-Pt02 (2Grp-Ptd02-baeq i)
