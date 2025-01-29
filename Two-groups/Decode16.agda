{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.cubical.PathPathOver
open import lib.cubical.PPOverFun
open import 2Grp
open import Codes
open import Decode0
open import Decode15

module Decode15 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  open CohGrp {{...}}

  decode : (z : K₂ η) → codes-fst z → base == z
  decode =
    K₂Elim loop
      (λ x → po-ext (loop x) (loop-decode x))
      (λ x y → ppo-ext (loop-comp x y) (loop-decode x) (loop-decode y) (loop-decode (mu x y)) (loop-comp-decode x y))
      (λ x y z →
        PPPOver-1type (loop-assoc x y z)
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

  decode-encode : (z : K₂ η) (p : base == z) → decode z (encode z p) == p
  decode-encode z idp = loop-ident

  loop-encode : loop ∘ encode base ∼ idf (base == base)
  loop-encode = decode-encode base

  loop-equiv : is-equiv loop
  loop-equiv = is-eq loop (encode base) loop-encode encode-loop
