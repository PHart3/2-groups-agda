{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4  #-}

open import lib.Basics
open import lib.NType2
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes
open import Decode2
open import Decode14

module Decode15 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  open WkMagNatIso

  module _ (x y z : G) where

    Λ =
      transport
        (λ v → loop (transport codes-fst (loop y) v) == loop v ∙ loop y)
        (! (↯ (transp-codes x z)))
        (ap loop (↯ (transp-codes y (mu z x))) ∙ ! (loop-comp (mu z x) y))
        
    abstract
      loop-comp-decode6-pre :
        Δ x y z ◃∙
        ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
        ap (transport (λ b → base == b) (loop y))
          (ap loop (transp-coe {B = codes-fst} (loop x) z ∙
                    ap (λ q → coe q z) (ap-∘ fst codes (loop x)) ∙
                    ap (λ q → coe q z) (θ codes-β x) ∙
                    coe-β ((λ v → mu v x) , mu-post-iso x) z)) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
        ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
        ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
          =ₛ
        Λ ◃∙
        ! (transp-cst=idf (loop y) (loop (transport codes-fst (loop x) z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (ap loop (↯ (transp-codes x z))) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (loop-comp z x)) ◃∙
        ap (transport (λ b → base == b) (loop y)) (! (transp-cst=idf (loop x) (loop z))) ◃∙
        ! (transp-∙ (loop x) (loop y) (loop z)) ◃∙
        ap (λ p → transport (λ b → base == b) p (loop z)) (loop-comp x y) ◃∎
      loop-comp-decode6-pre = =ₛ-in idp

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
    loop-comp-decode = loop-comp-decode05 x y z ∙ₛ (loop-comp-decode6-pre ∙ₛ loop-comp-decode6 x y z)
