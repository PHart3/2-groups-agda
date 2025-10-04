{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.NType2
open import lib.NConnected
open import lib.types.Sigma
open import lib.types.N-groups
open import lib.types.LoopSpace
open import lib.types.Pointed
open import lib.types.Truncation
open import 2Grp
open import 2GrpSIP
open import Hmtpy2Grp
open import LoopK-hom
open import 2Grp-bc
open import Delooping
open import Delooping-equiv
open import KLoop-adjeq
open import Sinh-classif

-- type equivalence between coherent 2-groups and Sinh triples

module Type-equiv-main (i : ULevel) where

 2G-Coh-Higher-≃ : 2Grp-tot i ≃ [ 2 , i ]-Groups
  -- 2Grp-tot (defined in 2Grp-bc) is the type of all coherent 2-groups
 2G-Coh-Higher-≃ = equiv
   (λ (G , η) → ⊙[ K₂ G η , base G {{η}} ] , ((K₂-is-conn G {{η}}) , (K₂-is-2type G {{η}})))
   (λ (X , _ , tr) → (Ω X) , (Loop2Grp (pt X) {{has-level-apply tr (pt X) (pt X)}}))
   (λ (X , cX , tX) → let instance _ = tX in
     pair=
       (⊙≃-to-== (K₂-rec-hom {{Loop2Grp (pt X)}} (pt X) {φ = idf (pt X == pt X)} idf2G , KLoop-is-equiv {{cX}}))
       prop-has-all-paths-↓)
   λ (_ , η) → ! (2grphom-to-== (loop-2g≃ {{η}}))

 2GrpCoh-Sinh-≃ : 2Grp-tot i ≃ Sinh-triples 1 i
 2GrpCoh-Sinh-≃ = NGrp-Sinh-≃ ∘e 2G-Coh-Higher-≃

 -- induced equivalence on connected components
 2GrpCoh-Sinh-≃-0 : Trunc 0 (2Grp-tot i) ≃ Sinh-triples-set 1 i
 2GrpCoh-Sinh-≃-0 = Sinh-classif-set ∘e Trunc-emap 2G-Coh-Higher-≃
