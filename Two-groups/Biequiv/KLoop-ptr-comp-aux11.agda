{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 --lossy-unification #-}

open import lib.Basics
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping
open import LoopK
open import KFunctor-comp
open import SqKLoop
open import apK
open import KLoop-ptr-comp-aux1
open import KLoop-ptr-comp-aux2
open import KLoop-ptr-comp-aux10

module KLoop-ptr-comp-aux11 where

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k}
  {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
  (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where

  open import KLoop-ptr-comp-defs2 f g x₀ x

  open KLPC-aux1 f g x₀ x
  open KLPC-aux2 f g x₀ x
  open KLPC-aux10 f g x₀ x

  abstract
    KLoop-∘-coher : Λ₀ =ₛ hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎
    KLoop-∘-coher = KLoop-∘-coher0 ∙ₛ (KLoop-∘-coher1 ∙ₛ KLoop-∘-coher2)

  abstract
    KLoop-∘-coher-out :
      hmtpy-nat-∙'
        (λ u →
          ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
          ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
          fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
          ! (ap (fst (K₂-rec-hom z₀ idf2G)) (fst (apK₂ {σ₁ = Loop2Grp-map-str (g ∘ f , idp)} (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
            fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
        (loop (x₀ == x₀) x)
        ==
      hmtpy-nat-∙' (λ u → idp) (loop (x₀ == x₀) x)
    KLoop-∘-coher-out = =ₛ-out KLoop-∘-coher
