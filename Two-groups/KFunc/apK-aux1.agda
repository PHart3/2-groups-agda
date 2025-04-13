{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Delooping
open import KFunctor

module apK-aux1 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f₁ f₂ : G₁ → G₂}
  {σ₁ : WkSGrpHomStr f₁} {σ₂ : WkSGrpHomStr f₂} where

  open WkSGrpNatIso
  open WkSGrpHomStr

  module _ (iso : WkSGrpNatIso (sgrphom-forg (cohsgrphom f₁ {{σ₁}})) (sgrphom-forg (cohsgrphom f₂ {{σ₂}})))
    (x y : G₁) where

    apK₂-coher1 = 
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      K₂-map-β-pts σ₁ (mu x y) ◃∙
      ap (loop G₂) (θ iso (mu x y)) ◃∙
      ! (K₂-map-β-pts σ₂ (mu x y)) ◃∎
        =ₛ⟨ 2 & 1 & K₂-map-β-comp σ₁ x y ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      ap (loop G₂) (map-comp σ₁ x y) ◃∙
      ap (loop G₂) (θ iso (mu x y)) ◃∙
      ! (K₂-map-β-pts σ₂ (mu x y)) ◃∎
        =ₛ⟨ 7 & 1 & ap-seq-=ₛ (loop G₂) (θ-comp-rot iso x y) ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      ap (loop G₂) (map-comp σ₁ x y) ◃∙
      ap (loop G₂) (! (map-comp σ₁ x y)) ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      ap (loop G₂) (map-comp σ₂ x y) ◃∙
      ! (K₂-map-β-pts σ₂ (mu x y)) ◃∎
        =ₛ⟨ 10 & 1 & !-=ₛ (K₂-map-β-comp σ₂ x y) ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      ap (loop G₂) (map-comp σ₁ x y) ◃∙
      ap (loop G₂) (! (map-comp σ₁ x y)) ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      ap (loop G₂) (map-comp σ₂ x y) ◃∙
      ! (ap (loop G₂) (map-comp σ₂ x y)) ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎ ∎ₛ
        
    apK₂-coher2 =
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      ap (loop G₂) (map-comp σ₁ x y) ◃∙
      ap (loop G₂) (! (map-comp σ₁ x y)) ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      ap (loop G₂) (map-comp σ₂ x y) ◃∙
      ! (ap (loop G₂) (map-comp σ₂ x y)) ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ₁⟨ 6 & 2 & ap-!-inv (loop G₂) (map-comp σ₁ x y) ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      ap (loop G₂) (map-comp σ₂ x y) ◃∙
      ! (ap (loop G₂) (map-comp σ₂ x y)) ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ₁⟨ 8 & 2 & !-inv-r (ap (loop G₂) (map-comp σ₂ x y)) ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
      ! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-r (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ⟩
      ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
      idp ◃∙
      ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ₁⟨ 0 & 3 & !-inv-r (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎ ∎ₛ

    apK₂-coher3 =
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      loop-comp G₂ (f₁ x) (f₁ y) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ⟨ 2 & 1 & ap2CommSq _ _ (loop-comp G₂) (θ iso x) (θ iso y) ⟩
      idp ◃∙
      ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ◃∙
      ap2 (λ a b → loop G₂ a ∙ loop G₂ b) (θ iso x) (θ iso y) ◃∙
      loop-comp G₂ (f₂ x) (f₂ y) ◃∙
      ! (ap2 (λ a b → loop G₂ (mu a b)) (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ap (loop G₂) (ap2 mu (θ iso x) (θ iso y)) ◃∙
      idp ◃∙
      ! (loop-comp G₂ (f₂ x) (f₂ y)) ◃∙
      ! (ap2 _∙_ (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y)) ◃∙
      ! (! (∙-ap (K₂-map σ₂) (loop G₁ x) (loop G₁ y))) ◃∙
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎ ∎ₛ
