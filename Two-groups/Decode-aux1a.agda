{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import 2Magma
open import 2Grp
open import Codes

module Decode-aux1a where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module Long-aux8-aux-aux2a (z : G) (p₁ : base == base) where

    abstract

      long-aux8-aux-aux2-aux0 :
        ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
          =ₛ
        ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      long-aux8-aux-aux2-aux0 = 
        ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
          =ₛ⟨ ap-∙-unit-r-nat loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ⟩
        ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ

      long-aux8-aux-aux2-aux1 :
        ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₛ
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      long-aux8-aux-aux2-aux1 = 
        ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₛ₁⟨ 0 & 1 & ! (!-! (∙-unit-r (loop (transport codes-fst p₁ z)))) ⟩
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ
