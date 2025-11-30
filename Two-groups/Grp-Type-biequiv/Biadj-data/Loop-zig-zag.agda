{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=6 #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import 2GrpMap
open import 2Semigroup
open import Hmtpy2Grp
open import KFunctor
open import LoopK-hom
import Delooping

-- the invertible modification making up the triangulator for our biadjoint biequivalence

open CohGrp {{...}}
open CohGrpHom
open WkSGrpNatIso
open WkSGrpHomStr

module Biadj-data.Loop-zig-zag where
{-
-- first component of triangulator
module _ {i} {X : Type i} {{ηX : has-level 2 X}} (x₀ : X) where

  open Delooping (Ω ⊙[ X , x₀ ])

  Loop-zz₀-iso : CohGrpNatIso
    (Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap)
    (cohgrphom _ {{idf2G {{Loop2Grp x₀}}}})
  θ Loop-zz₀-iso p = K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p
  θ-comp Loop-zz₀-iso x y = ! (=ₛ-out lemma)
    where abstract
      lemma :
        ! (ap2 _∙_
            (K₂-rec-hom-β-pts x₀ idf2G x)
            (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        map-comp
          (Loop2Grp-map (K₂-rec-hom x₀ idf2G) ∘2Gσ (cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap)) x y ◃∙
        K₂-rec-hom-β-pts x₀ idf2G (x ∙ y) ◃∎
          =ₛ
        idp ◃∎
      lemma = let K₂-rec-fun = fst (K₂-rec-hom x₀ idf2G) in  -- i.e., map (Loop2Grp-map (K₂-rec-hom x₀ idf2G)) 
        ! (ap2 _∙_
            (K₂-rec-hom-β-pts x₀ idf2G x)
            (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap  K₂-rec-fun) (ap (λ x → x) (loop-comp x y))) ◃∙
        K₂-rec-hom-β-pts x₀ idf2G (x ∙ y) ◃∎
          =ₛ⟨ 2 & 1 & K₂-rec-hom-β-comp x₀ idf2G x y ⟩
        ! (ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y)) ◃∙
        (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (ap (λ x → x) (loop-comp x y))) ◃∙
        ! (∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) (loop-comp x y)) ◃∙
        ap2 _∙_ (K₂-rec-hom-β-pts x₀ idf2G x) (K₂-rec-hom-β-pts x₀ idf2G y) ◃∙
        idp ◃∎
          =ₛ₁⟨ 1 & 1 & ap (λ p → ∙-ap K₂-rec-fun (loop x) (loop y) ∙ ap (ap K₂-rec-fun) p) (ap-idf (loop-comp x y)) ⟩
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

  Loop-zz₀ :
    Loop2Grp-map (K₂-rec-hom x₀ (idf2G {{Loop2Grp x₀}})) ∘2G cohgrphom _ {{idf2G {{Loop2Grp base}}}} ∘2G K₂-loopmap
      ==
    cohgrphom (idf (Ω ⊙[ X , x₀ ])) {{idf2G {{Loop2Grp x₀}}}}
  Loop-zz₀ = natiso2G-to-== Loop-zz₀-iso
-}
-- second component of triangulator
module _ {i j} {X : Type i} {Y : Type j} {{ηX : has-level 2 X}} {{ηY : has-level 2 Y}} (x₀ : X) (y₀ : Y)
  (f* : ⊙[ X , x₀ ] ⊙→ ⊙[ Y , y₀ ]) where

  open import SqKLoop
  
  open Delooping 

  Loop-zz₁-∼ : (p : x₀ == x₀) → 
    K₂-rec-hom-β-pts y₀ (idf2G {{Loop2Grp y₀}}) (Ω-fmap f* p) ∙
    ! (ap (Ω-fmap f*) (K₂-rec-hom-β-pts x₀ (idf2G {{Loop2Grp x₀}}) p)) ∙
    {!!} ∙ -- ! (∙-Ω-fmap (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) _ _) ∙
    Ω-fmap-ap (sq-KΩ x₀ y₀ f*) (loop (Ω ⊙[ X , x₀ ]) p) ∙
    ∙-Ω-fmap (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}})) (Ω-fmap {!K₂-map⊙ ?!} (loop (Ω ⊙[ X , x₀ ]) p)) {!!} ∙
    ap (Ω-fmap (K₂-rec-hom y₀ (idf2G {{Loop2Grp y₀}}))) (K₂-map-β-pts (str (Loop2Grp-map f*)) p) ∙
    idp
      ==
    idp
  Loop-zz₁-∼ p = {!!}
