{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor

module KFunctor-comp-aux3 where

open CohGrp {{...}}

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}} where

  module _ {f₁ : G₁ → G₂} (σ₁ : WkMagHomStr f₁) {f₂ : G₂ → G₃} (σ₂ : WkMagHomStr f₂) (x y : G₁) where

    open WkMagHomStr

    K₂-map-∘-coher3-aux4 :
      {b : K₂ G₁ η₁} (p₁ : base G₁ == b) (p₂ : b == base G₁)
      {t₁ : base G₃ == K₂-map σ₂ (K₂-map σ₁ b)}
      {t₂ : K₂-map σ₂ (K₂-map σ₁ b) == base G₃}
      (d₁ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) == t₁)
      (d₂ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₂) == t₂)
      → 
      ! (ap2 _∙_ d₁ d₂) ∙
      ! (! (∙-ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) (ap (K₂-map σ₁) p₂))) ∙
      ! (ap (ap (K₂-map σ₂)) (! (∙-ap (K₂-map σ₁) p₁ p₂) ∙ idp)) ∙
      (∘-ap (K₂-map σ₂) (K₂-map σ₁) (p₁ ∙ p₂) ∙
      ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (p₁ ∙ p₂)))) ∙ idp
        ==
      ap2 _∙_
        (! d₁ ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₁ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₁)))
        (! d₂ ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₂ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₂))) ∙
      ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp p₁ p₂ ∙ idp
    K₂-map-∘-coher3-aux4 idp p₂ idp idp = lemma p₂
      where
        lemma : {b : K₂ G₁ η₁} (p : b == base G₁) →
          (∘-ap (K₂-map σ₂) (K₂-map σ₁) p ∙ ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p))) ∙ idp
            ==
          ap2 _∙_ idp (∘-ap (K₂-map σ₂) (K₂-map σ₁) p ∙ ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p))) ∙
          ∙-assoc2-!-inv-l-aux (K₂-map σ₂ ∘ K₂-map σ₁) p idp idp idp ∙ idp
        lemma idp = idp

    K₂-map-∘-coher3-aux3 :
      (p₁ p₂ : base G₁ == base G₁)
      {x : base G₃ == base G₃}
      (ν : 
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ ∙
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂
          ==
        x)
      {f : base G₃ == base G₃}
      (α :
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ ∙
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂
          ==
        f)
      {g : base G₂ == base G₂}
      (s : ap (K₂-map σ₁) p₁ ∙ ap (K₂-map σ₁) p₂ == g)
      (d₁ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) == ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁)
      (d₂ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₂) == ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂)
      → 
      ν ∙
      ! ν ∙
      α ∙ ! α ∙
      ! (ap2 _∙_ d₁ d₂) ∙
      ! (! (∙-ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) (ap (K₂-map σ₁) p₂))) ∙
      ! (! (ap (ap (K₂-map σ₂)) s)) ∙
      ! (ap (ap (K₂-map σ₂)) (! (∙-ap (K₂-map σ₁) p₁ p₂) ∙ s ∙ idp)) ∙
      (∘-ap (K₂-map σ₂) (K₂-map σ₁) (p₁ ∙ p₂) ∙
      ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (p₁ ∙ p₂)))) ∙ idp
        ==
      ap2 _∙_
        (! d₁ ∙ ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₁ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₁)))
        (! d₂ ∙ ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₂ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₂))) ∙
      ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp p₁ p₂ ∙ idp
    K₂-map-∘-coher3-aux3 p₁ p₂ idp idp idp d₁ d₂ = K₂-map-∘-coher3-aux4 p₁ p₂ d₁ d₂

    K₂-map-∘-coher3-aux2 :
      (p₁ p₂ : base G₁ == base G₁)
      {h₁ : G₃} {h₂ : G₂}
      (μ₂ : h₂ == f₁ (mu x y)) (μ₁ : h₁ == f₂ h₂)
      (α :
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ ∙
        ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂
          ==
        loop G₃ h₁)
      (s : ap (K₂-map σ₁) p₁ ∙ ap (K₂-map σ₁) p₂ == loop G₂ h₂)
      (d₁ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) == ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁)
      (d₂ : ap (K₂-map σ₂) (ap (K₂-map σ₁) p₂) == ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂)
      → 
      ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ p₂ ∙
      ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ p₂) ∙
      α ∙
      ap (loop G₃) (μ₁ ∙ ap f₂ μ₂) ∙
      ! (ap (λ z → loop G₃ (f₂ z)) μ₂) ∙
      ! (ap (loop G₃) μ₁) ∙
      ! α ∙
      ! (ap2 _∙_ d₁ d₂) ∙
      ! (! (∙-ap (K₂-map σ₂) (ap (K₂-map σ₁) p₁) (ap (K₂-map σ₁) p₂))) ∙
      ! (! (ap (ap (K₂-map σ₂)) s)) ∙
      ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) μ₂ ∙
      ! (ap (ap (K₂-map σ₂))
          (! (∙-ap (K₂-map σ₁) p₁ p₂) ∙
          s ∙
          ap (loop G₂) μ₂)) ∙
      (∘-ap (K₂-map σ₂) (K₂-map σ₁) (p₁ ∙ p₂) ∙
      ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (p₁ ∙ p₂)))) ∙
      idp
        ==
      ap2 _∙_
        (! d₁ ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₁ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₁)))
        (! d₂ ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₂ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₂))) ∙
      ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp p₁ p₂ ∙
      idp
    K₂-map-∘-coher3-aux2 p₁ p₂ idp idp α s d₁ d₂ =
      K₂-map-∘-coher3-aux3 p₁ p₂
        (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ p₂)
        α s d₁ d₂

    private
      δ' : {p₁ p₂ p₃ : base G₁ == base G₁} (r : p₁ ∙ p₂ == p₃) → _
      δ' r = ap (λ p → ap (K₂-map σ₂ ∘ K₂-map σ₁) p ∙ idp) r

    K₂-map-∘-coher3-aux : (p₁ p₂ {p₃} : base G₁ == base G₁) (r : p₁ ∙ p₂ == p₃)
      {h₁ h₂ : base G₃ == base G₃}
      (t₁ : ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ == h₁)
      (t₂ : ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₂ == h₂)
      (α : h₁ ∙ h₂ == loop G₃ (mu (f₂ (f₁ x)) (f₂ (f₁ y))))
      {v₁ v₂ : base G₂ == base G₂} (c₁ : ap (K₂-map σ₁) p₁ == v₁) (c₂ : ap (K₂-map σ₁) p₂ == v₂)
      (s : v₁ ∙ v₂ == loop G₂ (mu (f₁ x) (f₁ y)))
      (d₁ : ap (K₂-map σ₂) v₁ == h₁) (d₂ : ap (K₂-map σ₂) v₂ == h₂)
      →
      ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ p₂ ∙
      ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) r ∙
      ! (ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) r) ∙
      ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) p₁ p₂) ∙
      ap2 _∙_
        t₁
        t₂ ∙
      α ∙
      ap (loop G₃) (map-comp σ₂ (f₁ x) (f₁ y) ∙ ap f₂ (map-comp σ₁ x y)) ∙
      ! (ap (λ z → loop G₃ (f₂ z)) (map-comp σ₁ x y)) ∙
      ! (ap (loop G₃) (map-comp σ₂ (f₁ x) (f₁ y))) ∙
      ! α ∙
      ! (ap2 _∙_ d₁ d₂) ∙
      ! (! (∙-ap (K₂-map σ₂) v₁ v₂)) ∙
      ! (! (ap (ap (K₂-map σ₂)) s)) ∙
      ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ∙
      ! (ap (ap (K₂-map σ₂))
          (! (ap (ap (K₂-map σ₁)) r) ∙
          ! (∙-ap (K₂-map σ₁) p₁ p₂) ∙
          ap2 _∙_ c₁ c₂ ∙
          s ∙
          ap (loop G₂) (map-comp σ₁ x y))) ∙
      ! (ap (λ z → ap (K₂-map σ₂) (ap (K₂-map σ₁) z)) r) ∙
      (∘-ap (K₂-map σ₂) (K₂-map σ₁) (p₁ ∙ p₂) ∙
      ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (p₁ ∙ p₂)))) ∙
      δ' r
        ==
      ap2 _∙_
        (t₁ ∙
         ! d₁ ∙
         ! (ap (ap (K₂-map σ₂)) c₁) ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₁ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₁)))
        (t₂ ∙
         ! d₂ ∙
         ! (ap (ap (K₂-map σ₂)) c₂) ∙
         ∘-ap (K₂-map σ₂) (K₂-map σ₁) p₂ ∙
         ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) p₂))) ∙
      ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp p₁ p₂ ∙
      δ' r
    K₂-map-∘-coher3-aux p₁ p₂ idp idp idp α idp idp s d₁ d₂ =
      K₂-map-∘-coher3-aux2 p₁ p₂ (map-comp σ₁ x y) (map-comp σ₂ (f₁ x) (f₁ y)) α s d₁ d₂

    abstract
      K₂-map-∘-coher3 :
        ∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y) ◃∙
        ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y) ◃∙
        ! (ap (ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}))) (loop-comp G₁ x y)) ◃∙
        ! (∙-ap (K₂-map (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}})) (loop G₁ x) (loop G₁ y)) ◃∙
        ap2 _∙_
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y) ◃∙ 
        loop-comp G₃ ((f₂ ∘ f₁) x) ((f₂ ∘ f₁) y) ◃∙
        ap (loop G₃) (map-comp (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x y) ◃∙
        ! (ap (λ z → loop G₃ (f₂ z)) (map-comp σ₁ x y)) ◃∙
        ! (ap (loop G₃) (map-comp σ₂ (f₁ x) (f₁ y))) ◃∙
        ! (loop-comp G₃ (f₂ (f₁ x)) (f₂ (f₁ y))) ◃∙
        ! (ap2 _∙_ (K₂-map-β-pts σ₂ (f₁ x)) (K₂-map-β-pts σ₂ (f₁ y))) ◃∙
        ! (! (∙-ap (K₂-map σ₂) (loop G₂ (f₁ x)) (loop G₂ (f₁ y)))) ◃∙
        ! (! (ap (ap (K₂-map σ₂)) (loop-comp G₂ (f₁ x) (f₁ y)))) ◃∙
        ap (λ z → ap (K₂-map σ₂) (loop G₂ z)) (map-comp σ₁ x y) ◃∙
        (! (ap (ap (K₂-map σ₂))
             (! (ap (ap (K₂-map σ₁)) (loop-comp G₁ x y)) ∙
             ! (∙-ap (K₂-map σ₁) (loop G₁ x) (loop G₁ y)) ∙
             ap2 _∙_ (K₂-map-β-pts σ₁ x) (K₂-map-β-pts σ₁ y) ∙
             loop-comp G₂ (f₁ x) (f₁ y) ∙
             ap (loop G₂) (map-comp σ₁ x y))) ∙
           (! (ap (λ z → ap (K₂-map σ₂) (ap (K₂-map σ₁) z)) (loop-comp G₁ x y)) ∙
           (∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x ∙ loop G₁ y) ∙
           ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x ∙ loop G₁ y)))) ∙
           δ' (loop-comp G₁ x y))) ◃∎
          =ₛ
        ap2 _∙_
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x ∙
            ! (K₂-map-β-pts σ₂ (f₁ x)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ∙
            ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ x))))
          ( K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y ∙
            ! (K₂-map-β-pts σ₂ (f₁ y)) ∙
            ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ y)) ∙
            ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ y) ∙
            ! (∙-unit-r (ap (K₂-map σ₂ ∘ K₂-map σ₁) (loop G₁ y)))) ◃∙
        ∙-assoc2-!-inv-l (K₂-map σ₂ ∘ K₂-map σ₁) idp idp (loop G₁ x) (loop G₁ y) ◃∙
        δ' (loop-comp G₁ x y) ◃∎
      K₂-map-∘-coher3 = =ₛ-in $
        K₂-map-∘-coher3-aux
          (loop G₁ x) (loop G₁ y) (loop-comp G₁ x y)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) x)
          (K₂-map-β-pts (cohgrphom f₂ {{σ₂}} ∘2Gσ cohgrphom f₁ {{σ₁}}) y)
          (loop-comp G₃ (f₂ (f₁ x)) (f₂ (f₁ y)))
          (K₂-map-β-pts σ₁ x)
          (K₂-map-β-pts σ₁ y)
          (loop-comp G₂ (f₁ x) (f₁ y))
          (K₂-map-β-pts σ₂ (f₁ x))
          (K₂-map-β-pts σ₂ (f₁ y))
