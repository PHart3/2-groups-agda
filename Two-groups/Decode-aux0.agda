{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import 2Magma
open import 2Grp
open import Codes

module Decode-aux0 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module _ (z : G) where
  
    long-aux8-aux-aux1 : {b : K₂ η} (p₁ : base == b) (p₂ : b == base) →
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
        ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
          (ap-∘ fst codes p₂) ∙ idp)) ∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z)
        ==
      idp
    long-aux8-aux-aux1 idp p₂ = aux (transp-coe p₂ z) (ap (λ q → coe q z) (ap-∘ fst codes p₂))
      where
        aux : {x₁ x₂ x₃ : G} (c₁ : x₁ == x₂) (c₂ : x₂ == x₃) →
          ! (ap loop (c₁ ∙ c₂ ∙ idp)) ∙ (ap loop c₁ ∙ ap loop c₂) ∙ idp == idp
        aux idp idp = idp
