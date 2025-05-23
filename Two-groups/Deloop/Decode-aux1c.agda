{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes

module Decode-aux1c where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Long-aux8-aux-aux2c (z : G) (p₁ : base == base) where

    private
      ϕ = ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z)))
      
    abstract    
      long-aux8-aux-aux2-aux3 :
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₛ
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        idp ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      long-aux8-aux-aux2-aux3 =
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
          =ₑ⟨ 2 & 1 & (idp ◃∙ ϕ ◃∎) % =ₛ-in (idp {a = ϕ}) ⟩
        ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
        ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        idp ◃∙
        ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ
