{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import LoopK

module KLoop-ptr-idf-aux2
  {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-idf-defs x₀ x

  abstract
    KLoop-ptr-idf-coher1 : Λ₁ =ₛ Λ₂
    KLoop-ptr-idf-coher1 = 
      Λ₁
        =ₛ₁⟨ 8 & 2 & ap-!-inv-l (ap (fst (K₂-rec-hom x₀ idf2G))) (K₂-map-β-pts (idf2G {{Loop2Grp x₀}}) x) ⟩
      Λ₂ ∎ₛ
