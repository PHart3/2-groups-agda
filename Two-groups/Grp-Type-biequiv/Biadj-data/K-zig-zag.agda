{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import SqLoopK
open import SqKLoop
open import LoopK-hom

-- second zig-zag modification for our biequivalence data

module Biadj-data.K-zig-zag where

import Delooping

module _ {i} {G : Type i} {{η : CohGrp G}} where 

  K₂-base-ty : Type i
  K₂-base-ty = K₂ (baseG == baseG) (Loop2Grp baseG) where
    open Delooping
    baseG : K₂ G η
    baseG = base G
  
  open Delooping G

  open CohGrpHom

  KLoop-fun : Delooping.K₂ (base == base) (Loop2Grp base) → K₂ η
  KLoop-fun = fst (K₂-rec-hom base (idf2G {{Loop2Grp base}}))

  K-zz : K₂-rec-hom base (idf2G {{Loop2Grp base}}) ⊙∘ K₂-map⊙ (str K₂-loopmap) ⊙-crd∼ ⊙idf ⊙[ K₂ η , base ]
  fst K-zz = 
    K₂-∼-ind
      (KLoop-fun ∘ K₂-map (str K₂-loopmap))
      (idf (K₂ η))
      idp
      {!!}
      {!!}
  snd K-zz = {!!}
