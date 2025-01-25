{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.NType2
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverFun
open import 2Magma
open import 2MagMap
open import 2Grp
open import 2GrpAutoEq
open import Hmtpy2Grp
open import Codes

module Decode where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  loop-decode : (x y : G) →
    loop (transport codes-fst (loop x) y)
      =-=
    transport (λ z → base == z) (loop x) (loop y)
  loop-decode x y = 
    loop (transport codes-fst (loop x) y)
      =⟪ ap loop (↯ (transp-codes x y)) ⟫
    loop (mu y x)
      =⟪ ! (loop-comp y x) ⟫
    loop y ∙ loop x
      =⟪ ! (transp-cst=idf (loop x) (loop y)) ⟫
    transport (λ z → base == z) (loop x) (loop y) ∎∎

  module _ (x y z : G) where

    
