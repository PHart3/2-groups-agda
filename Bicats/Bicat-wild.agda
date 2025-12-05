{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import Bicategory
open import lib.wild-cats.WildCats renaming
  (hom to homW; id₁ to id₁W; ρ to ρW; lamb to lambW; α to αW)

-- underlying wild category of bicategory

module Bicat-wild where

open BicatStr

bc-to-wc : ∀ {i j} → Bicat j i → WildCat {i} {j}
ob (bc-to-wc (B₀ , _)) = B₀
homW (bc-to-wc (_ , ξB)) = hom ξB
id₁W (bc-to-wc (_ , ξB)) = id₁ ξB
_▢_ (bc-to-wc (_ , ξB)) = _◻_ ξB
ρW (bc-to-wc (_ , ξB)) = ρ ξB
lambW (bc-to-wc (_ , ξB)) = lamb ξB
αW (bc-to-wc (_ , ξB)) h g f = α ξB h g f
