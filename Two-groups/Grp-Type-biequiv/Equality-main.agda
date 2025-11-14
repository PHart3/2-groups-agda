{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import AdjEq-exmps
open import 2Grp
open import 2Grp-bc
open import Ptd-bc
open import Bicat-iso
open import Bicat-quniv
open import Biequiv
open import Biequiv-main

-- Final theorem: two equalities between 2-groups and pointed connected 2-types, one from K₂ and one from Ω

module Equality-main (i : ULevel) where

  open CohGrpHom

  -- Both (2,1)-cats in question are quasi-univalent.

  qu-2G : is-quniv-bc (2grp-bicat i)
  qu-2G = univ-to-quniv univ-2G

  qu-Pt02 : is-quniv-bc (Ptd02-bicat i)
  qu-Pt02 = univ-to-quniv univ-Pt02

  -- final equality induced by K₂
  2Grp-Ptd02-eql-K₂ : (2Grp-tot i , 2grp-bicat i) == (Ptd02 i , Ptd02-bicat i)
  2Grp-Ptd02-eql-K₂ = biequiv-to-== qu-2G qu-Pt02 (2Grp-Ptd02-bieq i)

  -- final equality induced by Ω
  2Grp-Ptd02-eql-Ω : (Ptd02 i , Ptd02-bicat i) == (2Grp-tot i , 2grp-bicat i)
  2Grp-Ptd02-eql-Ω =
    -- first extract the reverse underlying wild equivalence
    let
      equiv-wc_rev = Equiv-wc-reverse (beqv-to-niso (2Grp-Ptd02-bieq i))
      open Psfunctor
    in
    iso-bc-to-== (BiequivStr-inst.Ψ₂ (2Grp-Ptd02-bieq i) ,
      is-eq (map-pf (BiequivStr-inst.Ψ₂ (2Grp-Ptd02-bieq i))) (map-pf (BiequivStr-inst.Ψ₁ (2Grp-Ptd02-bieq i)))
        (λ G → qu-2G (AdjEq-rev (_ , BiequivStr-inst.lev-eq₂ (2Grp-Ptd02-bieq i) G)))
        (λ X → qu-Pt02 (_ , (BiequivStr-inst.lev-eq₁ (2Grp-Ptd02-bieq i) X))) ,
      λ x y → Equiv-wc-ff equiv-wc_rev {x} {y})
  
