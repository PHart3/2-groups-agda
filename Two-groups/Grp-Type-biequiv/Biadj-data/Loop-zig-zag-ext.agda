{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=7 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping

-- the invertible modification making up the triangulator for our biadjoint biequivalence

module Biadj-data.Loop-zig-zag-ext where

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

-- first component (in an extensional form) of triangulator
module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open Delooping (Ω ⊙[ X , x₀ ])

  Loop-zz₀-iso : CohGrpNatIso
    ((Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}}) ∘2G K₂-loopmap)
    (cohgrphom _ {{idf2G {{Loop2Grp x₀}}}})
  θ Loop-zz₀-iso p = K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p
  θ-comp Loop-zz₀-iso x y = ! (=ₛ-out lemma)
    where abstract
      lemma :
        ! (ap2 _∙_
            (K₂-rec-hom-β-pts x₀ idf2G x)
            (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
         map-comp
          ((Loop2Grp-map (K₂-rec-hom x₀ idf2G) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}}) ∘2Gσ K₂-loopmap) x y ◃∙
        K₂-rec-hom-β-pts x₀ idf2G (x ∙ y) ◃∎
          =ₛ
        idp ◃∎
      lemma = let K₂-rec-fun = fst (K₂-rec-hom x₀ idf2G) in  -- i.e., map (Loop2Grp-map (K₂-rec-hom x₀ idf2G)) 
        ! (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        ((∙-ap K₂-rec-fun (loop x) (loop y) ∙ idp) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        K₂-rec-hom-β-pts x₀ idf2G (x ∙ y) ◃∎
          =ₛ⟨ 2 & 1 & K₂-rec-hom-β-comp x₀ idf2G x y ⟩
        ! (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        ((∙-ap K₂-rec-fun (loop x) (loop y) ∙ idp) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        ! (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y) ◃∙
        idp ◃∎
          =ₛ₁⟨ 1 & 1 & ap (λ p → p ∙ ap (ap K₂-rec-fun) (loop-comp x y))
            (∙-unit-r (∙-ap K₂-rec-fun (loop x) (loop y))) ⟩
        ! (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        ! (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y) ◃∙
        idp ◃∎
          =ₛ⟨ 1 & 2 & !-inv-r◃ (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ⟩
        ! (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y) ◃∙
        idp ◃∎
          =ₛ⟨ 0 & 2 & !-inv-l◃ (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ⟩
        idp ◃∎ ∎ₛ

-- second component (in an extensional form) of triangulator
module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} {x₀ : X} {y₀ : Y} where

  open import SqKLoop
  open import K-hom-ind
  open import LoopFunctor-ap

  open import Biadj-data.Loop-zig-zag-ext-aux
  
  open Delooping (Ω ⊙[ X , x₀ ])

  abstract
    Loop-zz₁-∼ : (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) (p : x₀ == x₀) → 
      ((! (θ (Loop2Grp-map-∘ f* (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
      θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)) ∙
      θ (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f*))) (loop p)) ∙
      ap (Ω-fmap (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map-β-pts (Loop2Grp-map-str f*) p)
        ==
      ap (Ω-fmap f*) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (Ω-fmap f* p))
    Loop-zz₁-∼ f*@(f , idp) p = =ₛ-out $
      ((! (θ (Loop2Grp-map-∘ f* (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
      θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)) ∙
      θ (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f*))) (loop p)) ◃∙
      ap (Ω-fmap (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₑ⟨ 0 & 1 &
            (! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
            θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)) ◃∙
            ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∎
          % =ₛ-in (idp {a =
            (! (θ (Loop2Grp-map-∘ f* (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
            θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)) ∙
            θ (Loop2Grp-map-∘ (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (K₂-map⊙ (Loop2Grp-map-str f*))) (loop p)}) ⟩
      (! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
      θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)) ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₑ⟨ 0 & 1 &
            (! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
            θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p) ◃∎)
          % =ₛ-in (idp {a =
            ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ∙
            θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p)}) ⟩
      ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
      θ (Loop2Grp-map-ap (sq-KΩ x₀ y₀ f*)) (loop p) ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ₁⟨ 1 & 1 & Loop2Grp-map-ap-fst (sq-KΩ x₀ y₀ f*) (loop p) ⟩
      ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
      Ω-fmap-ap (sq-KΩ x₀ y₀ f*) (loop p) ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ⟨ 1 & 1 & Ω-fmap-ap-hnat (sq-KΩ x₀ y₀ f*) (loop p) ⟩
      ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
      idp ◃∙
      ap (λ q → q) (hmtpy-nat-∙' (fst (sq-KΩ x₀ y₀ f*)) (loop p)) ◃∙
      idp ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ₁⟨ 1 & 2 & ap-idf (hmtpy-nat-∙' (fst (sq-KΩ x₀ y₀ f*)) (loop p)) ⟩
      ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
      hmtpy-nat-∙' (fst (sq-KΩ x₀ y₀ f*)) (loop p) ◃∙
      idp ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ⟨ 1 & 1 & sq-KΩ-K₂-β p f ⟩
      ! (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ◃∙
      ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p) ◃∙
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p)) ◃∙
      ! (ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p)) ◃∙
      idp ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ⟨ 0 & 2 & !-inv-l◃ (ap-∘ f (fst (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}}))) (loop p)) ⟩
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p)) ◃∙
      ! (ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p)) ◃∙
      idp ◃∙
      ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p) ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ₁⟨ 3 & 3 &
          !-inv-l (ap-∘ (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map (Loop2Grp-map-str f*)) (loop p)) ⟩
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p)) ◃∙
      ! (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p)) ◃∙
      idp ◃∙
      ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p) ◃∎
        =ₛ₁⟨ 2 & 3 &
          !-inv-l (ap (ap (fst (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})))) (K₂-map-β-pts (Loop2Grp-map-str f*) p)) ⟩
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p)) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 3 & ∙-unit-r (! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p))) ⟩
      ap (ap f) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p) ◃∙
      ! (K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (ap f p)) ◃∎ ∎ₛ
