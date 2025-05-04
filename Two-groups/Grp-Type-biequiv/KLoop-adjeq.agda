{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.NConnected
open import homotopy.Loop-conn-equiv
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import Delooping-equiv
open import Ptd-bc
open import AdjEq
open import AdjEq-exmps

module KLoop-adjeq where

module _ {i} {X : Ptd i} {{cX : is-connected 0 (de⊙ X)}} {{tX : has-level 2 (de⊙ X)}} where

   abstract
     KLoop-is-equiv : is-equiv (fst (K₂-rec-hom {{Loop2Grp (pt X)}} (pt X) {φ = idf (pt X == pt X)} idf2G))
     KLoop-is-equiv = Ω-conn-≃  {{cX = K₂-is-conn (pt X == pt X)}}
       (K₂-rec-hom {{Loop2Grp (pt X)}} (pt X) {φ = idf (pt X == pt X)} idf2G)
       (3-for-2-e _ (ΩK₂-hom (pt X) idf2G) loop-equiv (idf-is-equiv (pt X == pt X)))

     KLoop-adjeq-str : Adjequiv {a = _ , (K₂-is-conn (pt X == pt X) , K₂-is-2type (pt X == pt X))} $
       K₂-rec-hom {{Loop2Grp (pt X)}} (pt X) {φ = idf (pt X == pt X)} idf2G
     KLoop-adjeq-str =
       ⊙≃-to-adjeq {X = _ , (K₂-is-conn (pt X == pt X) , K₂-is-2type (pt X == pt X))}
       (K₂-rec-hom {{Loop2Grp (pt X)}} (pt X) {φ = idf (pt X == pt X)} idf2G , KLoop-is-equiv)
       {c = cX} {t = tX}
