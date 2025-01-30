{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode-aux4b
open import Decode-aux4c
open import Decode-aux4d
open import Decode-aux4b-defs

module Decode-aux4e where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    open Decode-defs4b z p₁ p₂ q₂
    open Decode4b z p₁ p₂ q₂
    open Decode4c z p₁ p₂ q₂
    open Decode4d z p₁ p₂ q₂

    abstract
      long-aux7b : τ₁ =ₛ τ₂
      long-aux7b = long-aux7b0 ∙ₛ (long-aux7b1 ∙ₛ long-aux7b2)
