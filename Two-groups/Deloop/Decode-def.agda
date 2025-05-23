{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pi
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverFun
open import 2Grp
open import Codes
open import Decode0
open import Decode15

module Decode-def where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  open CohGrp {{...}}

  private 
    A =
      (λ x y z →
        PPPOver-1type
          (loop-assoc x y z)
          ( ∙ᵈ-assoc-ppo (po-ext (loop x) (loop-decode x)) (po-ext (loop y) (loop-decode y)) (po-ext (loop z) (loop-decode z)) ∙ᶜ
            ap-∙-preᶜ (po-ext (loop x) (loop-decode x))
              (ppo-ext (loop-comp y z) (loop-decode y) (loop-decode z) (loop-decode (mu y z)) (loop-comp-decode y z)) ∙ᶜ
            (ppo-ext (loop-comp x (mu y z)) (loop-decode x) (loop-decode (mu y z))
              (loop-decode (mu x (mu y z))) (loop-comp-decode x (mu y z))) )
          ( ap-∙-postᶜ (po-ext (loop z) (loop-decode z))
              (ppo-ext (loop-comp x y) (loop-decode x) (loop-decode y) (loop-decode (mu x y)) (loop-comp-decode x y)) ∙ᶜ
            (ppo-ext (loop-comp (mu x y) z) (loop-decode (mu x y)) (loop-decode z) (loop-decode (mu (mu x y) z))
              (loop-comp-decode (mu x y) z)) ∙ᶜ
            !ᶜ (apd-po (λ x → po-ext (loop x) (loop-decode x)) (al x y z)) ))

  decode : (z : K₂ η) → codes-fst z → base == z
  decode =
    K₂-elim loop
      (λ x → po-ext (loop x) (loop-decode x))
      (λ x y →
        ppo-ext {p₁ = loop x} (loop-comp x y) (loop-decode x) (loop-decode y) (loop-decode (mu x y)) (loop-comp-decode x y))
      A
