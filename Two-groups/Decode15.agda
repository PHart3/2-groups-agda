{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode2
open import Decode10
open import Decode14

module Decode15 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module _ (x y z : G) where

    abstract
      loop-comp-decode05 :
        ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
        ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
        ap loop (↯ (transp-codes (mu x y) z)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
          =ₛ
        transport
          (λ v → loop (transport codes-fst (loop y) v) == loop v ∙ loop y)
          (! (↯ (transp-codes x z)))
          (ap loop (↯ (transp-codes y (mu z x))) ∙ ! (loop-comp (mu z x) y)) ◃∙
        ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
        ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
        ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎ 
      loop-comp-decode6 = loop-comp-decode04 x y z ∙ₛ loop-comp-decode5 x y z
      
    abstract
      loop-comp-decode : 
        ! (ap loop (transp-∙ (loop x) (loop y) z)) ◃∙
        ap loop (ap (λ p → transport codes-fst p z) (loop-comp x y)) ◃∙
        ap loop (↯ (transp-codes (mu x y) z)) ◃∙
        ! (loop-comp z (mu x y)) ◃∙
        ! (transp-cst=idf (loop (mu x y)) (loop z)) ◃∎
          =ₛ
        ap loop (↯ (transp-codes y (transport codes-fst (loop x) z))) ◃∙
        ! (loop-comp (transport codes-fst (loop x) z) y) ◃∙
        ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
        ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
        ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
      loop-comp-decode = loop-comp-decode05 x y z ∙ₛ loop-comp-decode6 x y z
