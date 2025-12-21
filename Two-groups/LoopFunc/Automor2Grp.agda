{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.Univalence2
open import lib.types.Sigma
open import 2Grp
open import Bicategory
open import AdjEq
open import Univ-bc

module Automor2Grp where

-- adjoint autoequivalence 2-group of an object in a bicategory

open BicatStr {{...}}
open CohGrp

Aut-adj-2G : ∀ {i j} {C : Type i} {{ξC : BicatStr j C}} (x : C) → CohGrp (AdjEquiv ξC x x)
1trunc (Aut-adj-2G x) = Σ-level-instance {{⟨⟩}} {{prop-has-level-S ae-unique.Adjequiv-is-prop}}
id (Aut-adj-2G x) = AdjEq-id₁
mu (Aut-adj-2G x) = {!!}
lam (Aut-adj-2G x) = {!!}
rho (Aut-adj-2G x) = {!!}
al (Aut-adj-2G x) = {!!}
tr (Aut-adj-2G x) = {!!}
pent (Aut-adj-2G x) = {!!}
inv (Aut-adj-2G x) = AdjEq-rev
linv (Aut-adj-2G x) = {!!}
rinv (Aut-adj-2G x) = {!!}
zz₁ (Aut-adj-2G x) = {!!}
zz₂ (Aut-adj-2G x) = {!!}
