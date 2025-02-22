{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import K-hom-ind
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-idf
open import KFunctor-comp

module KLoop-ptr-comp where

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (x₀ : X) (y₀ : Y) (z₀ : Z) where

  private  
    Λx₀ = wkmag-to-loop x₀ (cohmaghom (idf (x₀ == x₀)) {{idf2G}})
    Λy₀ = wkmag-to-loop y₀ (cohmaghom (idf (y₀ == y₀)) {{idf2G}})
    Λz₀ = wkmag-to-loop z₀ (cohmaghom (idf (z₀ == z₀)) {{idf2G}})
    K₂-rec-x₀ = K₂-rec (x₀ == x₀) x₀ (loop' Λx₀) (loop-comp' Λx₀) (loop-assoc' Λx₀)
    K₂-rec-y₀ = K₂-rec (y₀ == y₀) y₀ (loop' Λy₀) (loop-comp' Λy₀) (loop-assoc' Λy₀)
    K₂-rec-z₀ = K₂-rec (z₀ == z₀) z₀ (loop' Λz₀) (loop-comp' Λz₀) (loop-assoc' Λz₀)

  
