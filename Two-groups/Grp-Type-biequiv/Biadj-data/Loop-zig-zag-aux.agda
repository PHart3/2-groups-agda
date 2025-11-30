{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
open import SqKLoop
open import K-hom-ind
import Delooping

module Biadj-data.Loop-zig-zag-aux where

module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X}
  (p : x₀ == x₀) (f : X → Y) where
  
  open Delooping (Ω ⊙[ X , x₀ ])

  private
    y₀ = f x₀
    ν =
      (λ p →
        ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p) ∙
        ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ∙
        ! (K₂-rec-hom-β-pts y₀ idf2G (ap f p)) ∙
        ! (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) p)) ∙
        ! (ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop p)))

  abstract
    sq-KΩ-K₂-β : 
      hmtpy-nat-∙' (fst (sq-KΩ x₀ y₀ (f , idp))) (loop p) ◃∎
        =ₛ
      ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p) ◃∙
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ idf2G (ap f p)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str (f , idp)) p)) ◃∙
      ! (ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str (f , idp))) (loop p)) ◃∎
    sq-KΩ-K₂-β = =ₛ-in $
      K₂-∼-ind-β
        (f ∘ K₂-rec-x₀ x₀ y₀)
        (K₂-rec-y₀ x₀ y₀ ∘ K₂-map (Loop2Grp-map-str (f , idp)))
        idp
        ν
        _ p
