{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import 2SGrpMap
open import Hmtpy2Grp
import Delooping
open import Biadj-data.Loop-zig-zag-aux1
open import Biadj-data.Loop-zig-zag-aux2c

-- the invertible modification making up the triangulator for our biadjoint biequivalence

module Biadj-data.Loop-zig-zag where

open import Biadj-data.Loop-zig-zag-defs public

-- Recall the first component: Loop-zz₀ = natiso2G-to-== (Loop-zz₀-iso x₀)

-- second component of triangulator
module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y}
  (f : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where
  
  open Delooping
  open Loop-zz-defs f
  open Loop-zz-aux1 f
  open Loop-zz-aux2c f
  
  abstract
    Loop-zz₁ : ρ₁ =ₛ ρ₂      
    Loop-zz₁ =
      ρ₁
        =ₛ⟨ ρ₁-translate ⟩
      natiso-to-== ρ₁-trans ◃∎
        =ₛ₁⟨ ap natiso-to-== (natiso∼-to-== (Loop-zz₁-∼ f)) ⟩
      natiso-to-== ρ₂-trans ◃∎
        =ₛ⟨ !ₛ ρ₂-translate ⟩
      ρ₂ ∎ₛ

