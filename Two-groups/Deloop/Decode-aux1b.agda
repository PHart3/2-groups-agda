{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes

module Decode-aux1b where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Long-aux8-aux-aux2b (z : G) (p₁ : base == base) where

    abstract
      long-aux8-aux-aux2-aux2 :
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₛ
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      long-aux8-aux-aux2-aux2 = 
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₛ₁⟨ 1 & 1 & ! (ap-idf (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))) ⟩
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ
