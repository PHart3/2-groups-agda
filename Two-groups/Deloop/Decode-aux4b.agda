{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux0
open import Decode-aux4b-defs

module Decode-aux4b where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Decode4b (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Decode-defs4b z p₁ p₂ q₂

    long-aux7b0 =
      τ₁
        =ₑ⟨ 2 & 6 & (idp ◃∎) % =ₛ-in (long-aux8-aux-aux1 z p₁ p₂) ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      idp ◃∙
      ! q₂ ◃∙
      idp ◃∎ ∎ₛ
