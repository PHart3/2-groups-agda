{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux2
open import Decode-aux4b-defs

module Decode-aux4d where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Decode4d (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Decode-defs4b z p₁ p₂ q₂

    long-aux7b2 =
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      idp ◃∎
        =ₛ₁⟨ ∙-unit-r
               (ap (λ v → loop v ∙ p₂)
                 (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
        =ₛ⟨ long-aux8-aux-aux2 z p₁ p₂ ⟩
      τ₂ ∎ₛ
