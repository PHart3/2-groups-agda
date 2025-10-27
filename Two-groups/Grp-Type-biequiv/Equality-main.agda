{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import 2Grp
open import 2Grp-bc
open import 2GrpSIP
open import Ptd-bc
open import Bicat-wild
open import Bicat-iso
open import Bicat-quniv
open import Biequiv
open import Biequiv-main

-- Final theorem: two equalities between 2-groups and pointed connected 2-types, one from K₂ and one from Ω

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
  
