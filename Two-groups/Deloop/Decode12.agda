{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode11

module Decode12 where

-- an ad-hoc lemma used below
module _ {i} {A : Type i} where

  transp-cst-∙ : {x₁ x₂ x₃ : A} (p₁ : x₁ == x₂) (p₂ : x₂ == x₃) (p₃ : x₂ == x₁) →
    transp-cst=idf p₂ (p₃ ∙ p₁) ◃∎
      =ₛ
    (ap (transport (_==_ x₂) p₂) (! (transp-cst=idf p₁ p₃)) ∙
    ! (transp-∙ p₁ p₂ p₃) ∙ idp) ◃∙
    ! (∙-assoc p₃ p₁ p₂ ∙ ! (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎
  transp-cst-∙ {x₁} idp idp p₃ = =ₛ-in (aux p₃)
    where
      aux : {x : A} (p : x₁ == x) → 
        ! (∙-unit-r (p ∙ idp))
          ==
        (ap (transport (_==_ x₁) idp) (! (! (∙-unit-r p))) ∙ idp) ∙
        ! (∙-assoc p idp idp ∙ ! (! (∙-unit-r p)))
      aux idp = idp

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ p₃ : base == base) where

    module _
      (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
      (q₃ : p₃ ∙ p₁ == loop (coe (ap fst (ap codes p₁)) z)) where

      private
        μ = transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp
        τ =
          transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
            (! μ)
              (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
                ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
                  (ap-∘ fst codes p₂) ∙ idp) ∙
               ! q₂)

      long-aux5 :
        τ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        transp-cst=idf p₂ (p₃ ∙ p₁) ◃∎
          =ₛ
        τ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        (ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
        ! (transp-∙ p₁ p₂ p₃) ∙ idp) ◃∙
        ! (∙-assoc p₃ p₁ p₂ ∙ ! (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎
      long-aux5 = 
        τ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        transp-cst=idf p₂ (p₃ ∙ p₁) ◃∎
          =ₛ⟨ 4 & 1 & transp-cst-∙ p₁ p₂ p₃ ⟩
        τ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        (ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
        ! (transp-∙ p₁ p₂ p₃) ∙ idp) ◃∙
        ! (∙-assoc p₃ p₁ p₂ ∙ ! (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎ ∎ₛ

      private
        β = ! (ap (λ p → p ∙ p₂) q₃)
        
      abstract
        long-aux4-aux :
          ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
          (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
          ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
          ap loop (ap (λ q → coe q z)
            (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
              ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
          ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
          ! q₂ ◃∙
          β ◃∎
            =ₛ
          τ ◃∙
          ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
          ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
          ap (transport (_==_ base) p₂) (! q₃) ◃∙
          (ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
          ! (transp-∙ p₁ p₂ p₃) ∙ idp) ◃∙
          ! (∙-assoc p₃ p₁ p₂ ∙ ! (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎
        long-aux4-aux = long-aux6 z p₁ p₂ q₂ q₃ ∙ₛ long-aux5

      long-aux4 :
        ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
        (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
        ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
            ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
        ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
        ! q₂ ◃∙
        β ◃∙
        (∙-assoc p₃ p₁ p₂ ∙ ! (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎
          =ₛ
        τ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂) (ap loop μ) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        (ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
        ! (transp-∙ p₁ p₂ p₃) ∙ idp) ◃∎
      long-aux4 = post-rotate-out long-aux4-aux
