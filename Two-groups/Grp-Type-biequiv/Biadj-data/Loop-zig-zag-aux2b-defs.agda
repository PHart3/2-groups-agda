{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2GrpMap-conv
open import 2SGrpMap
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-defs

module Biadj-data.Loop-zig-zag-aux2b-defs where

module Loop-zz-aux2b-defs {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-defs f

  τ₀ :
    Loop2Grp-map f ∘2G
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    (K₂-loopmap (Ω ⊙[ X , x₀ ]))
      ==
    Loop2Grp-map f ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}
  τ₀ =
    natiso2G-to-==
      {μ =
        Loop2Grp-map f ∘2G
        (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G
        cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
        (K₂-loopmap _)}
      {ν =
        Loop2Grp-map f ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}}
      (natiso-whisk-l {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso x₀))

  τ₁ :
    (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
    cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
    Loop2Grp-map f
      ==
    ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
    cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
    (K₂-loopmap (Ω ⊙[ Y , y₀ ]))) ∘2G
    Loop2Grp-map f
  τ₁ =
    natiso2G-to-==
      {μ =
        (cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}} ∘2G
        cohgrphom (idf (Ω ⊙[ Y , y₀ ])) {{idf2G {{Loop2Grp y₀}}}}) ∘2G
        Loop2Grp-map f}
      {ν =
        ((Loop2Grp-map (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) ∘2G
        cohgrphom _ {{idf2G {{Loop2Grp (base _)}}}}) ∘2G
        (K₂-loopmap _)) ∘2G
        Loop2Grp-map f}
      (!ʷ (natiso-whisk-r {μ = grphom-forg (Loop2Grp-map f)} (Loop-zz₀-iso y₀)))
