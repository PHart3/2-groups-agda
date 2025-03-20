{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import 2Grp
open import Codes
open import Hmtpy2Grp
open import 2GrpSIP
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

  loop-equiv : is-equiv loop
  loop-equiv = is-eq loop (encode base) loop-encode encode-loop

  -- Main delooping theorem: loop is an equivalence of 2-groups.
  loop-2g≃ : η 2g≃ Loop2Grp base
  fst loop-2g≃ = loop , loop-equiv
  snd loop-2g≃ = CohGrpHom.str K₂-loopmap
