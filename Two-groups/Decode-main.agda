{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Decode0
open import Decode16

module Decode-main where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  open CohGrp {{...}}

  decode-encode : (z : K₂ η) (p : base == z) → decode z (encode z p) == p
  decode-encode z idp = loop-ident

  loop-encode : loop ∘ encode base ∼ idf (base == base)
  loop-encode = decode-encode base

  -- main delooping theorem
  loop-equiv : is-equiv loop
  loop-equiv = is-eq loop (encode base) loop-encode encode-loop
