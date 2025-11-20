{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import Bicat-wild
open import Biadj
open import Pstransf-SIP
open import Biequiv

module Biadj-props where

open BicatStr {{...}}
open Pstrans

module _ {i₁ i₂ j₁ j₂} {B@(B₀ , _) : Bicat j₁ i₁} {C@(C₀ , _) : Bicat j₂ i₂} where

  private
    instance
      ξB : BicatStr j₁ B₀
      ξB = snd B
      ξC : BicatStr j₂ C₀
      ξC = snd C

  open BiequivStr-inst
  open Equiv-wc

  module _ (be : BiequivStr ξB ξC) (ba : Biadj-data (τ₁ be) (τ₂ be)) where


--    ζzz₂-to-ζzz₁ : 
