{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes

module Decode-aux4a-defs where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module Decode-defs4a (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    σ₁ =
      ! (transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
        (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂)) ◃∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      idp ◃∎

    σ₂ =
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
        ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
          (ap-∘ fst codes p₂) ∙ idp)) ◃∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      idp ◃∎
