{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=2 --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import 2Grp
open import Bicategory
open import AdjEqv
open import Univ-bc
open import WkEqv-bc-ops
open import AdjEqv-SIP

-- adjoint autoequivalence 2-group (or automorphism 2-group) of an object in a bicategory

module Automor2Grp where

open BicatStr {{...}}
open CohGrp
open Adjequiv

Aut-adj-2G : ∀ {i j} {C : Type i} {{ξC : BicatStr j C}} (x : C) → CohGrp (AdjEquiv ξC x x)
1trunc (Aut-adj-2G x) = Σ-level-instance {{⟨⟩}} {{prop-has-level-S ae-unique.Adjequiv-is-prop}}
id (Aut-adj-2G x) = AdjEqv-id₁
mu (Aut-adj-2G x) g f = g AdjEqv-∘ f
lam (Aut-adj-2G x) (f , _) = pair= (! (lamb f)) prop-has-all-paths-↓
rho (Aut-adj-2G x) (f , _) = pair= (! (ρ f)) prop-has-all-paths-↓
al (Aut-adj-2G x) (h , _) (g , _) (f , _) = pair= (α h g f) prop-has-all-paths-↓
tr (Aut-adj-2G x) f g =
  AdjEqv-whisk-r {α₁ = f AdjEqv-∘ AdjEqv-id₁ } {α₂ = f} (pair (! (ρ (fst f))) _) g ∙
  ! (ap2 _∙_ (Σ-! _) (AdjEqv-whisk-l {α₁ = AdjEqv-id₁ AdjEqv-∘ g} {α₂ = g} (pair (! (lamb (fst g))) _) f) ∙
  Σ-∙ _ _ ∙
  pair== (! (=ₛ-out (tri-bc◃-rot5 (fst g) (fst f)))) (prop-has-all-paths-↓ {{↓-preserves-level ⟨⟩}}))
pent (Aut-adj-2G x) i h g f =
  Σ-∙{p = α (fst i) (fst h) (fst g ◻ fst f)} {p' = α (fst i ◻ fst h) (fst g) (fst f)} _ _ ∙
  ! (ap2 (λ p₁ p₂ → p₁ ∙ pair= (α (fst i) (fst h ◻ fst g) (fst f)) prop-has-all-paths-↓ ∙ p₂)
      (AdjEqv-whisk-l (pair (α (fst h) (fst g) (fst f)) _) i) (AdjEqv-whisk-r (pair (α (fst i) (fst h) (fst g)) _) f) ∙
  ap (λ p → pair= (ap (λ m → fst i ◻ m) (α (fst h) (fst g) (fst f))) prop-has-all-paths-↓ ∙ p)
    (Σ-∙ {p = α (fst i) (fst h ◻ fst g) (fst f) } {p' = ap (λ m → m ◻ fst f) (α (fst i) (fst h) (fst g))} _ _) ∙
  Σ-∙ _ _ ∙
  pair== (! (pent-bc (fst f) (fst g) (fst h) (fst i))) (prop-has-all-paths-↓ {{↓-preserves-level ⟨⟩}}))
inv (Aut-adj-2G x) = AdjEqv-rev
linv (Aut-adj-2G x) (_ , ae) = pair= (! (eta ae)) prop-has-all-paths-↓
rinv (Aut-adj-2G x) (_ , ae) = pair= (eps ae) prop-has-all-paths-↓
zz₁ (Aut-adj-2G x) f = ! $
  ap3 (λ p₁ p₂ p₃ → p₁ ∙ p₂ ∙ p₃ ∙ pair= (! (ρ (fst f))) prop-has-all-paths-↓)
    (AdjEqv-whisk-r (pair (eps (snd f)) _) f)
    (Σ-! {p = α (fst f) (inv (snd f)) (fst f)} _)
    (AdjEqv-whisk-l (pair (! (eta (snd f))) _) f) ∙
  ap (λ p →
    pair= (ap (λ m → m ◻ fst f) (eps (snd f)))
      {b' = snd ((f AdjEqv-∘ –> AdjEqv-rev-≃ f) AdjEqv-∘ f)} prop-has-all-paths-↓ ∙
    pair= (! (α (fst f) (inv (snd f)) (fst f))) (!ᵈ prop-has-all-paths-↓) ∙
    p)
    (Σ-∙ {p = ap (λ m → fst f ◻ m) (! (eta (snd f)))} {p' = ! (ρ (fst f))} _ _) ∙
  ap (λ p → pair= (ap (λ m → m ◻ fst f) (eps (snd f))) prop-has-all-paths-↓ ∙ p)
    (Σ-∙ {p = ! (α (fst f) (inv (snd f)) (fst f))} {p' = ap (λ m → fst f ◻ m) (! (eta (snd f))) ∙ ! (ρ (fst f))} _ _) ∙
  Σ-∙
    {p = ap (λ m → m ◻ fst f) (eps (snd f))}
    {p' = ! (α (fst f) (inv (snd f)) (fst f)) ∙ ap (λ m → fst f ◻ m) (! (eta (snd f))) ∙ ! (ρ (fst f))}
    _ _ ∙
  pair== (=ₛ-out (coher-map-rot4 (snd f))) (prop-has-all-paths-↓ {{↓-preserves-level ⟨⟩}})
zz₂ (Aut-adj-2G x) f =
  Σ-! {p = ! (lamb (inv (snd f)))} _ ∙
  ! (ap3 (λ p₁ p₂ p₃ → p₁ ∙ p₂ ∙ pair= (α (inv (snd f)) (fst f) (inv (snd f))) prop-has-all-paths-↓ ∙ p₃)
      (Σ-! {p = ! (ρ (inv (snd f)))} _)
      (AdjEqv-whisk-l (pair (eps (snd f)) _) (AdjEqv-rev f))
      (AdjEqv-whisk-r (pair (! (eta (snd f))) _) (AdjEqv-rev f)) ∙
    Σ-∙3
      (! (! (ρ (inv (snd f))))) (!ᵈ prop-has-all-paths-↓)
      (ap (λ m → inv (snd f) ◻ m) (eps (snd f))) _
      (α (inv (snd f)) (fst f) (inv (snd f))) _
      (ap (λ m → m ◻ inv (snd f)) (! (eta (snd f)))) _ ∙
    pair== (=ₛ-out aux) (prop-has-all-paths-↓ {{↓-preserves-level ⟨⟩}}))
    where abstract
      aux :
        ! (! (ρ (inv (snd f)))) ◃∙
        ap (λ m → inv (snd f) ◻ m) (eps (snd f)) ◃∙
        α (inv (snd f)) (fst f) (inv (snd f)) ◃∙
        ap (λ m → m ◻ inv (snd f)) (! (eta (snd f))) ◃∎
          =ₛ
        ! (! (lamb (inv (snd f)))) ◃∎
      aux =
        ! (! (ρ (inv (snd f)))) ◃∙
        ap (λ m → inv (snd f) ◻ m) (eps (snd f)) ◃∙
        α (inv (snd f)) (fst f) (inv (snd f)) ◃∙
        ap (λ m → m ◻ inv (snd f)) (! (eta (snd f))) ◃∎
          =ₛ₁⟨ 0 & 1 & !-! (ρ (inv (snd f))) ⟩
        ρ (inv (snd f)) ◃∙
        ap (λ m → inv (snd f) ◻ m) (eps (snd f)) ◃∙
        α (inv (snd f)) (fst f) (inv (snd f)) ◃∙
        ap (λ m → m ◻ inv (snd f)) (! (eta (snd f))) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-! (λ m → m ◻ inv (snd f)) (eta (snd f)) ⟩
        ρ (inv (snd f)) ◃∙
        ap (λ m → inv (snd f) ◻ m) (eps (snd f)) ◃∙
        α (inv (snd f)) (fst f) (inv (snd f)) ◃∙
        ! (ap (λ m → m ◻ inv (snd f)) (eta (snd f))) ◃∎
          =ₛ⟨ coher-inv-rot3 (snd f) ⟩
        lamb (inv (snd f)) ◃∎
          =ₛ₁⟨ ! (!-! (lamb (inv (snd f)))) ⟩
        ! (! (lamb (inv (snd f)))) ◃∎ ∎ₛ
