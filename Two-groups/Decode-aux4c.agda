{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes

module Decode-aux4c where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Decode4c (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    long-aux7b1 :
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      idp ◃∙
      ! q₂ ◃∙
      idp ◃∎
        =ₛ
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      idp ◃∎
    long-aux7b1 = =ₛ-in $
      ap (λ p →
        ap (λ v → loop v ∙ p₂)
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ∙ p)
        (ap (λ p → q₂ ∙ p) (∙-unit-r (! q₂)) ∙ !-inv-r q₂)
