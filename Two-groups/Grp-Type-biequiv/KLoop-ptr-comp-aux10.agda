{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import SqKLoop
open import LoopK-hom
open import KLoop-ptr-comp-red
open import KLoop-ptr-comp-aux3
open import KLoop-ptr-comp-aux4
open import KLoop-ptr-comp-aux5
open import KLoop-ptr-comp-aux6
open import KLoop-ptr-comp-aux7
open import KLoop-ptr-comp-aux8
open import KLoop-ptr-comp-aux9

module KLoop-ptr-comp-aux10 where

module KLPC-aux10 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs f g x₀ x
  open import KLoop-ptr-comp-defs2 f g x₀ x

  open KLPC-aux3 f g x₀ x
  open KLPC-aux4 f g x₀ x
  open KLPC-aux5 f g x₀ x
  open KLPC-aux6 f g x₀ x
  open KLPC-aux7 f g x₀ x
  open KLPC-aux8 f g x₀ x
  open KLPC-aux9 f g x₀ x

  abstract
    KLoop-∘-coher2-aux : {b : _} (p : base (x₀ == x₀) == b) →
      ! (ap (λ q → q) (! (ap-∘ (K₂-rec-y₀ x₀ z₀) (K₂-map (Loop2Grp-map-str (g ∘ f , idp))) p))) ∙
      ap (λ q → q) (! (ap (λ q → q) (ap-∘ (fst (K₂-rec-hom z₀ idf2G)) (λ z → fst (K₂-map⊙ (Loop2Grp-map-str (g ∘ f , idp))) z) p)))
        ==
      hmtpy-nat-∙' (λ u → idp) p
    KLoop-∘-coher2-aux idp = idp

  abstract
    KLoop-∘-coher2 : Λ₃ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎
    KLoop-∘-coher2 =
      Reduce◃28
        (=ₛ-out β-pts-red1)
        (=ₛ-out β-pts-red2)
        (=ₛ-out β-pts-red3)
        (=ₛ-out β-pts-red4)
        (=ₛ-out β-pts-red5)
        (=ₛ-out β-pts-red6)
        (=ₛ-out β-pts-red7)
        (KLoop-∘-coher2-aux (loop (x₀ == x₀) x))
