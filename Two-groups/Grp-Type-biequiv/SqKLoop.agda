{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import SqKLoop-lossy

module SqKLoop where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y) where

  open SqKL-defs x₀ y₀ public

  sq-KΩ : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) →
    f* ⊙∘ K₂-rec-hom {{Loop2Grp x₀}} x₀ (idf2G {{Loop2Grp x₀}})
      ⊙-comp
    K₂-rec-hom {{Loop2Grp y₀}} y₀ (idf2G {{Loop2Grp y₀}}) ⊙∘ K₂-map⊙ (Loop2Grp-map-str f*)
  sq-KΩ f* = sq-KΩ-lossy x₀ y₀ f*
