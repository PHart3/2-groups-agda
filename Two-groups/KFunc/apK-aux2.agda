{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 --lossy-unification #-}

open import lib.Basics
open import 2Semigroup
open import 2Grp
open import Delooping
open import KFunctor
open import apK-aux0
open import apK-aux1

module apK-aux2 where

open CohGrp {{...}}

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {f₁ f₂ : G₁ → G₂}
  {σ₁ : WkSGrpHomStr f₁} {σ₂ : WkSGrpHomStr f₂} where

  open WkSGrpNatIso
  open WkSGrpHomStr

  module _ (iso : WkSGrpNatIso (sgrphom-forg (cohsgrphom f₁ {{σ₁}})) (sgrphom-forg (cohsgrphom f₂ {{σ₂}})))
    (x y : G₁) where

    apK₂-coher3-aux : (q₁ q₂ : base G₁ == base G₁)
      {c₁ c₂ c₃ c₄ : G₂} (p₁ : c₁ == c₂) (p₂ : c₃ == c₄)
      {z₁ z₂ z₃ : base G₂ == base G₂}
      (r₁ : loop G₂ c₂ ∙ loop G₂ c₄ == loop G₂ (mu c₂ c₄)) (r₂ : ap (K₂-map σ₂) (q₁ ∙ q₂) == z₁)
      (τ₁ : z₂ == loop G₂ c₁) (τ₂ : z₃ == loop G₂ c₃)
      (δ₁ : ap (K₂-map σ₂) q₁ == loop G₂ c₂) (δ₂ : ap (K₂-map σ₂) q₂ == loop G₂ c₄)
      →
      ap2 _∙_ τ₁ τ₂ ∙
      ap2 (λ a b → loop G₂ a ∙ loop G₂ b) p₁ p₂ ∙
      r₁ ∙
      ! (ap2 (λ a b → loop G₂ (mu a b)) p₁ p₂) ∙
      ap (loop G₂) (ap2 mu p₁ p₂) ∙
      ! r₁ ∙
      ! (ap2 _∙_ δ₁ δ₂) ∙
      ! (! (∙-ap (K₂-map σ₂) q₁ q₂)) ∙
      ! (! r₂)
        ==
      ap2 _∙_
        (τ₁ ∙ ap (loop G₂) p₁ ∙ ! δ₁)
        (τ₂ ∙ ap (loop G₂) p₂ ∙ ! δ₂) ∙
      ∙-assoc2-!-inv-l (K₂-map σ₂) idp idp q₁ q₂ ∙
      r₂
    apK₂-coher3-aux q₁ q₂ {c₁} {c₃ = c₃} idp idp r₁ idp idp idp δ₁ δ₂ = =ₛ-out $
      r₁ ◃∙
      ! r₁ ◃∙
      ! (ap2 _∙_ δ₁ δ₂) ◃∙
      (! (! (∙-ap (K₂-map σ₂) q₁ q₂)) ∙ idp) ◃∎
        =ₛ₁⟨ 0 & 2 & !-inv-r r₁ ⟩
      idp ◃∙
      ! (ap2 _∙_ δ₁ δ₂) ◃∙
      (! (! (∙-ap (K₂-map σ₂) q₁ q₂)) ∙ idp) ◃∎
        =ₛ₁⟨ 0 & 2 & !-ap2 _∙_ δ₁ δ₂ ⟩
      ap2 _∙_ (! δ₁) (! δ₂) ◃∙
      (! (! (∙-ap (K₂-map σ₂) q₁ q₂)) ∙ idp) ◃∎
        =ₛ₁⟨ 1 & 1 & lemma q₁ q₂ ⟩
      ap2 _∙_ (! δ₁) (! δ₂) ◃∙
      (∙-assoc2-!-inv-l (K₂-map σ₂) idp idp q₁ q₂ ∙ idp) ◃∎ ∎ₛ
      where
        lemma : {b : K₂ G₁ η₁} (t₁ : base G₁ == b) (t₂ : b == base G₁)
          → ! (! (∙-ap (K₂-map σ₂) t₁ t₂)) ∙ idp == ∙-assoc2-!-inv-l (K₂-map σ₂) idp idp t₁ t₂ ∙ idp
        lemma idp t₂ = ∙-assoc2-!-inv-l-aux-idp3 (K₂-map σ₂) t₂ ∙ ! (∙-unit-r (∙-assoc2-!-inv-l-aux (K₂-map σ₂) t₂ idp idp idp)) 

    apK₂-coher4 =
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
      ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))) ◃∎
        =ₛ⟨ =ₛ-in $
          apK₂-coher3-aux
            (loop G₁ x) (loop G₁ y)
            (θ iso x) (θ iso y)
            (loop-comp G₂ (f₂ x) (f₂ y)) (ap (ap (K₂-map σ₂)) (loop-comp G₁ x y))
            (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y)
            (K₂-map-β-pts σ₂ x) (K₂-map-β-pts σ₂ y) ⟩
      ap2 _∙_
        (K₂-map-β-pts σ₁ x ∙ ap (loop G₂) (θ iso x) ∙ ! (K₂-map-β-pts σ₂ x))
        (K₂-map-β-pts σ₁ y ∙ ap (loop G₂) (θ iso y) ∙ ! (K₂-map-β-pts σ₂ y)) ◃∙
      ∙-assoc2-!-inv-l (fst (K₂-map⊙ σ₂)) idp idp (loop G₁ x) (loop G₁ y) ◃∙
      ap (ap (fst (K₂-map⊙ σ₂))) (loop-comp G₁ x y) ◃∎ ∎ₛ

    abstract
      apK₂-coher :
        ∙-ap (fst (K₂-map⊙ σ₁)) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (fst (K₂-map⊙ σ₁))) (loop-comp G₁ x y) ◃∙
        (K₂-map-β-pts σ₁ (mu x y) ∙ ap (loop G₂) (θ iso (mu x y)) ∙ ! (K₂-map-β-pts σ₂ (mu x y))) ◃∎
          =ₛ
        ap2 _∙_
          (K₂-map-β-pts σ₁ x ∙ ap (loop G₂) (θ iso x) ∙ ! (K₂-map-β-pts σ₂ x))
          (K₂-map-β-pts σ₁ y ∙ ap (loop G₂) (θ iso y) ∙ ! (K₂-map-β-pts σ₂ y)) ◃∙
        ∙-assoc2-!-inv-l (fst (K₂-map⊙ σ₂)) idp idp (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (fst (K₂-map⊙ σ₂))) (loop-comp G₁ x y) ◃∎
      apK₂-coher = apK₂-coher0 iso x y ∙ₛ apK₂-coher1 iso x y ∙ₛ apK₂-coher2 iso x y ∙ₛ apK₂-coher3 iso x y ∙ₛ apK₂-coher4
