{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import Delooping

module SqLoopK where

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  open CohGrp {{...}}
  open WkMagNatIso
  open WkMagHomStr

  sq-ΩK : {f : G₁ → G₂} (σ : CohGrpHomStr f)
    → CohGrpNatIso (Loop2Grp-map (K₂-map σ , idp) ∘2G K₂-loopmap G₁) (K₂-loopmap G₂ ∘2G cohgrphom f {{σ}})
  θ (sq-ΩK {f} σ) x = K₂-map-β-pts σ x
  θ-comp (sq-ΩK {f} σ) x y = ! (=ₛ-out lemma)
    where abstract
      lemma :
        ! (ap2 mu (K₂-map-β-pts σ x) (K₂-map-β-pts σ y)) ◃∙
        (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ∙ ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
        K₂-map-β-pts σ (mu x y) ◃∎
          =ₛ
        (loop-comp G₂ (f x) (f y) ∙ ap (loop G₂) (map-comp σ x y)) ◃∎
      lemma = 
        ! (ap2 mu (K₂-map-β-pts σ x) (K₂-map-β-pts σ y)) ◃∙
        (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ∙ ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
        K₂-map-β-pts σ (mu x y) ◃∎
          =ₛ⟨ 2 & 1 & K₂-map-β-comp σ x y ⟩
        ! (ap2 mu (K₂-map-β-pts σ x) (K₂-map-β-pts σ y)) ◃∙
        (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ∙ ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
        ! (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_ (K₂-map-β-pts σ x) (K₂-map-β-pts σ y) ◃∙
        loop-comp G₂ (f x) (f y) ◃∙
        ap (loop G₂) (map-comp σ x y) ◃∎
          =ₑ⟨ 1 & 1 & (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ◃∙ ap (ap (K₂-map σ)) (loop-comp G₁ x y) ◃∎) % =ₛ-in idp ⟩
        ! (ap2 mu (K₂-map-β-pts σ x) (K₂-map-β-pts σ y)) ◃∙
        ∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map σ)) (loop-comp G₁ x y) ◃∙
        ! (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_ (K₂-map-β-pts σ x) (K₂-map-β-pts σ y) ◃∙
        loop-comp G₂ (f x) (f y) ◃∙
        ap (loop G₂) (map-comp σ x y) ◃∎
          =ₛ₁⟨ 2 & 2 & !-inv-r (ap (ap (K₂-map σ)) (loop-comp G₁ x y)) ⟩
        _
          =ₛ₁⟨ 1 & 3 & !-inv-r (∙-ap (K₂-map σ) (loop G₁ x) (loop G₁ y)) ⟩
        _
          =ₛ₁⟨ 0 & 3 & !-inv-l (ap2 _∙_ (K₂-map-β-pts σ x) (K₂-map-β-pts σ y)) ⟩
        idp ◃∙
        loop-comp G₂ (f x) (f y) ◃∙
        ap (loop G₂) (map-comp σ x y) ◃∎
          =ₛ₁⟨ idp ⟩
        (loop-comp G₂ (f x) (f y) ∙ ap (loop G₂) (map-comp σ x y)) ◃∎ ∎ₛ
