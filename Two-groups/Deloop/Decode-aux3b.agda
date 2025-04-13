{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux3a

module Decode-aux3b where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Long-aux8 z p₁ p₂ q₂

    abstract
      long-aux8-aux :
        ! (transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
          (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
          (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
            ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
              (ap-∘ fst codes p₂) ∙ idp) ∙
           ! q₂)) ◃∎
          =ₛ
        ap (λ v → loop v ∙ p₂)
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
        q₂ ◃∙
        ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp)) ◃∙
        ! (ap (λ v → loop (transport codes-fst p₂ v))
            (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∎
      long-aux8-aux = long-aux8-aux0 ∙ₛ long-aux8-aux1
