{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import 2SGrpMap
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-defs
open import Biadj-data.Loop-zig-zag-aux0

module Biadj-data.Loop-zig-zag-aux1 where

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

module Loop-zz-aux1 {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}}
  {x₀ : X} {y₀ : Y} {f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]} where

  open import SqKLoop
  open import SqLoopK
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux0 public

  abstract
    ρ₁-translate :
      ρ₁
        =ₛ
      {!!}
    ρ₁-translate = {!!}
