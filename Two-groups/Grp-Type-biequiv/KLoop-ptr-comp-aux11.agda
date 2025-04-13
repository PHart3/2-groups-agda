{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK-hom
open import KFunctor-comp
open import SqKLoop
open import apK
open import KLoop-ptr-comp-aux1
open import KLoop-ptr-comp-aux2
open import KLoop-ptr-comp-aux10

module KLoop-ptr-comp-aux11 where

module KLPC-aux11 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x
  open import KLoop-ptr-comp-defs2 f g x₀ x

  open KLPC-aux1 f g x₀ x
  open KLPC-aux2 f g x₀ x
  open KLPC-aux10 f g x₀ x

  abstract
    KLoop-∘-coher :
      Λ₀
        =ₛ
      hmtpy-nat-∙'
        (λ u → idp {a = fst (K₂-rec-hom z₀ (idf2G {{Loop2Grp z₀}})) (K₂-map (Loop2Grp-map-str (g ∘ f , idp)) u)})
        (loop (x₀ == x₀) x) ◃∎
    KLoop-∘-coher = KLoop-∘-coher0 ∙ₛ KLoop-∘-coher1 ∙ₛ KLoop-∘-coher2
