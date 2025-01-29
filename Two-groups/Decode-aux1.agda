{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import 2Magma
open import 2Grp
open import Codes

module Decode-aux1 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  module _ (z : G) (p₁ : base == base) where
{-
    long-aux8-aux-aux2-aux0 = 
      ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
        =ₛ⟨ ap-∙-unit-r-nat loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ⟩
      ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ

    long-aux8-aux-aux2-aux1 =
      ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎

      ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ

    long-aux8-aux-aux2-aux01 :
      ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
        =ₛ
      ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ
    long-aux8-aux-aux2-aux01 = long-aux8-aux-aux2-aux0 ∙ₛ long-aux8-aux-aux2-aux1
-}

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
      ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
        =ₛ⟨ ap-∙-unit-r-nat loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ⟩
      ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (!-! (∙-unit-r (loop (transport codes-fst p₁ z)))) ⟩
      ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
      ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (ap-idf (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))) ⟩
      ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
      ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
        =ₑ⟨ 2 & 1 & (idp ◃∙ ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎) % =ₛ-in idp ⟩
      ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
      ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      idp ◃∙
      ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ


