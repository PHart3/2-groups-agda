{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux4a-defs
open import Decode-aux3

module Decode-aux4a where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Decode-defs4a z p₁ p₂ q₂

    abstract
      long-aux7a : σ₁ =ₛ σ₂
      long-aux7a = 
        σ₁
          =ₑ⟨ 0 & 1 &
            (ap (λ v → loop v ∙ p₂)
              (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
            q₂ ◃∙
            ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
              ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
                (ap-∘ fst codes p₂) ∙ idp)) ◃∙
            ! (ap (λ v → loop (transport codes-fst p₂ v))
              (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∎)
            % long-aux8-aux z p₁ p₂ q₂ ⟩
        σ₂ ∎ₛ
