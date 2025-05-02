{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Pointed
open import AdjEq
open import 2Grp
open import 2Grp-bc
open import 2GrpSIP
open import Ptd-bc
open import Bicat-quniv
open import Biequiv-main

-- Final theorem: an equality between 2-groups and pointed connected 2-types

module Equality-main (i : ULevel) where

  open Adjequiv
  open CohGrpHom

  -- Both (2,1)-cats in question are quasi-univalent.

  qu-2G : is-quniv-bc (2grp-bicat i)
  qu-2G {(_ , η₁)} {(_ , η₂)} (f , ae) =
    let instance
          _ : CohGrp _
          _ = η₁
          _ : CohGrp _
          _ = η₂
    in
      2grphom-to-== (equiv (map f)
        (map (inv ae))
          (λ x  → ! (app= (ap map (eps ae)) x))
          (λ x → ! (app= (ap map (eta ae)) x)) ,
        str f)

  Ptd-to-Ptd02-== : {X Y : Ptd02 i} → fst X ⊙≃ fst Y → X == Y
  Ptd-to-Ptd02-== e = pair= (⊙≃-to-== e) prop-has-all-paths-↓

  qu-Pt02 : is-quniv-bc (Ptd02-bicat i)
  qu-Pt02 (f , ae) = Ptd-to-Ptd02-==
    (f , (is-eq (fst f) (fst (inv ae))
      (λ x → ! (app= (fst= (eps ae)) x))
      λ x → ! (app= (fst= (eta ae)) x)))

  -- final equality
  2Grp-Ptd02-eql : 2grp-bicat i == Ptd02-bicat i
  2Grp-Ptd02-eql = biequiv-to-== qu-2G qu-Pt02 (2Grp-Ptd02-bieq i)
