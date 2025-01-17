{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import 2Magma

module 2MagMap where

open WkMag {{...}}

module _ {i} {G₁ : Type i} {{η₁ : WkMag G₁}} where

{-

natiso is id sys.
whiskering, associativity, unit law for nat isos.
equational syntax for nat isos.
composite of triangles

-}
