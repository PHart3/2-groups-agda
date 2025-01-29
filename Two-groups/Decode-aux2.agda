{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import 2Magma
open import 2Grp
open import Codes
open import Decode-aux1a
open import Decode-aux1b

module Decode-aux1 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module _ (z : G) (p₁ : base == base) where

    open Long-aux8-aux-aux2a z p₁
    open Long-aux8-aux-aux2b z p₁

    abstract
      long-aux8-aux-aux2 : {b : K₂ η} (p₂ : base == b) →
        ap (λ v → loop v ∙ p₂)
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
          =ₛ
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂)
          (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        idp ◃∙      
        transp-cst=idf p₂ (loop (coe (ap fst (ap codes p₁)) z)) ◃∎
      long-aux8-aux-aux2 idp =
        long-aux8-aux-aux2-aux0 ∙ₛ (long-aux8-aux-aux2-aux1 ∙ₛ (long-aux8-aux-aux2-aux2 ∙ₛ long-aux8-aux-aux2-aux3))
