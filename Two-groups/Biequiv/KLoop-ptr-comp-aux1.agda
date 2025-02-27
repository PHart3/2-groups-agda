{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics

module KLoop-ptr-comp-aux1 where

  module KLPC-aux1 {i j k} {X : Type i} {Y : Type j} {Z : Type k}
    {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {{ηZ : has-level 2 Z}}
    (f : X → Y) (g : Y → Z) (x₀ : X) (x : x₀ == x₀) where
    
    open import KLoop-ptr-comp-defs2 f g x₀ x

    abstract
      KLoop-∘-coher0 : Λ₀ =ₛ Λ₁
      KLoop-∘-coher0 = ρ₁

{-
    abstract
      KLoop-∘-coher :
        hmpty-nat-∙'
          (λ u →
            ! (fst (sq-KΩ x₀ z₀ (g ∘ f , idp)) u) ∙
            ap g (fst (sq-KΩ x₀ y₀ (f , idp)) u) ∙
            fst (sq-KΩ y₀ z₀ (g , idp)) (fst (K₂-map⊙ (Loop2Grp-map-str (f , idp))) u) ∙
            ! (ap (fst (K₂-rec-hom z₀ idf2G)) (fst (apK₂ (Loop2Grp-map-∘ (g , idp) (f , idp))) u ∙
              fst (K₂-map-∘ (Loop2Grp-map-str (f , idp)) (Loop2Grp-map-str (g , idp))) u)))
          (loop (x₀ == x₀) x) ◃∎
          =ₛ
        hmpty-nat-∙' (λ u → idp) (loop (x₀ == x₀) x) ◃∎ 
      KLoop-∘-coher = ?
-}
