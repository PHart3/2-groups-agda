{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux4a-defs
open import Decode-aux4b-defs
open import Decode-aux4a
open import Decode-aux4e

module Decode11 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Decode-defs4a z p₁ p₂ q₂
    open Decode-defs4b z p₁ p₂ q₂

    abstract
      long-aux7 : σ₁ =ₛ τ₂
      long-aux7 = long-aux7a z p₁ p₂ q₂ ∙ₛ long-aux7b z p₁ p₂ q₂

    module ends {t : base == base} (q₃ : t == loop (coe (ap fst (ap codes p₁)) z)) where

      private
        η₁ = ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))
        η₂ = ! (ap (λ p → p ∙ p₂) q₃)
        
      ε₁ =
        ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
        (ap loop (transp-coe (p₁ ∙ p₂) z) ∙ η₁) ◃∙
        ap loop (ap (λ q → coe q z)
          (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
            ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
        ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
        ! q₂ ◃∙
        η₂ ◃∎

      private
        η₃ =
          transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
            (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
            (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
              ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
                (ap-∘ fst codes p₂) ∙ idp) ∙
             ! q₂)
             
      ε₂ =
        η₃ ◃∙
        ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
        ap (transport (_==_ base) p₂)
          (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
        ap (transport (_==_ base) p₂) (! q₃) ◃∙
        transp-cst=idf p₂ t ◃∎

    open ends

    long-aux6 : {t : base == base} (q₃ : t == loop (coe (ap fst (ap codes p₁)) z))    
      → ε₁ q₃ =ₛ ε₂ q₃
    long-aux6 idp = pre-rotate'-out long-aux7
