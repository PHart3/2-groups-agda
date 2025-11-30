{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping
open import Biadj-data.Loop-zig-zag-ext

-- the invertible modification making up the triangulator for our biadjoint biequivalence

module Biadj-data.Loop-zig-zag where

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

-- first component of triangulator
module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open Delooping (Ω ⊙[ X , x₀ ])
  
  Loop-zz₀ :
    Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap
      ==
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}
  Loop-zz₀ = natiso2G-to-== (Loop-zz₀-iso x₀)

-- second component of triangulator
module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y)  where

  open import SqKLoop
  
  open Delooping (Ω ⊙[ X , x₀ ])

  abstract
    Loop-zz₁ : {!!}
    Loop-zz₁ = {!!}
