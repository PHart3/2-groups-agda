{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import Codes

module LoopK where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ {j} {X : Type j} {{ηX : has-level 2 X}} (x : X)
    {φ : G → x == x} where

    K₂-rec-hom : WkMagHomStr {{mag η}} {{mag (Loop2Grp x)}} φ → K₂ η → X
    K₂-rec-hom ρ =
      let Λ = loop2mag-conv x (cohmaghom φ {{ρ}}) in
        K₂-rec x (loop' Λ) (loop-comp' Λ) (loop-assoc' Λ)

    ΩK₂-hom : (ρ : WkMagHomStr {{mag η}} {{mag (Loop2Grp x)}} φ) → Ω-fmap (K₂-rec-hom ρ , idp) ∘ loop ∼ φ
    ΩK₂-hom ρ z =
      let Λ = loop2mag-conv x (cohmaghom φ {{ρ}}) in
        loop-βr x (loop' Λ) (loop-comp' Λ) (loop-assoc' Λ) z
