{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics

module KLoop-ptr-comp-aux1 where

module KLPC-aux1 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs2 f g x₀ x
  open import KLoop-ptr-comp-defs3 f g x₀ x

  abstract
    KLoop-∘-coher0 : Λ₀ =ₛ Λ₁
    KLoop-∘-coher0 = ρ₁
