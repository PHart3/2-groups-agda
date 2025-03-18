{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.FTID
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma
open import 2MagMap

module NatIso where

open WkMag {{...}}
open WkMagNatIso

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}}
  {μ₁ μ₂ : WkMagWkHom {{η₁}} {{η₂}}} where

  =WkMagNatIso : (ι ρ : WkMagNatIso μ₁ μ₂) → Type (lmax i j)
  =WkMagNatIso ι ρ = Σ (θ ι == θ ρ) (λ e → θ-comp ι == θ-comp ρ [ _ ↓ e ])

  module _ {ι ρ : WkMagNatIso μ₁ μ₂} where

    =WkMagNatIso→ : (ι == ρ) → =WkMagNatIso ι ρ
    fst (=WkMagNatIso→ idp) = idp
    snd (=WkMagNatIso→ idp) = idp

    =WkMagNatIso← : =WkMagNatIso ι ρ → (ι == ρ)
    =WkMagNatIso← (idp , idp) = idp

    =WkMagNatIso←→ : (e : ι == ρ) → =WkMagNatIso← (=WkMagNatIso→ e) == e
    =WkMagNatIso←→  idp = idp

    =WkMagNatIso→← : (e : =WkMagNatIso ι ρ) → =WkMagNatIso→ (=WkMagNatIso← e) == e
    =WkMagNatIso→← (idp , idp) = idp

  module _ {ι ρ : WkMagNatIso μ₁ μ₂} where

    =WkMagNatIso-econv : (ι == ρ) ≃ =WkMagNatIso ι ρ
    =WkMagNatIso-econv = 
      equiv
        =WkMagNatIso→
        =WkMagNatIso←
        =WkMagNatIso→←
        =WkMagNatIso←→ 

    =WkMagNatIso∼ : =WkMagNatIso ι ρ ≃ (θ ι ∼ θ ρ)
    =WkMagNatIso∼ = 
      equiv
        (λ (e₁ , e₂) x → app= e₁ x)
        (λ H → (λ= H) , prop-has-all-paths-↓ {{Π-level-instance}} )
        (λ b → λ= (app=-β b))
        λ a → pair= (! (λ=-η (fst a))) (prop-has-all-paths-↓ {{↓-level}})

  abstract
    natiso∼-contr : (ι : WkMagNatIso μ₁ μ₂) → is-contr (Σ (WkMagNatIso μ₁ μ₂) (λ ρ → θ ι ∼ θ ρ))
    natiso∼-contr ι = equiv-preserves-level aux
      where
        aux :
          Σ (WkMagNatIso μ₁ μ₂) (λ ρ → ι == ρ)
          ≃
          Σ (WkMagNatIso μ₁ μ₂) (λ ρ → θ ι ∼ θ ρ)
        aux = Σ-emap-r (λ _ → =WkMagNatIso∼ ∘e =WkMagNatIso-econv)

  module _ {ι : WkMagNatIso μ₁ μ₂} where

    natiso∼-ind : ∀ {k} (P : (ρ : WkMagNatIso μ₁ μ₂) → θ ι ∼ θ ρ →  Type k)
      → P ι (λ z → idp) → {ρ : WkMagNatIso μ₁ μ₂} (p : θ ι ∼ θ ρ) → P ρ p
    natiso∼-ind P = ID-ind-map P (natiso∼-contr ι)

    natiso∼-to-== : {ρ : WkMagNatIso μ₁ μ₂} → θ ι ∼ θ ρ → ι == ρ
    natiso∼-to-== = natiso∼-ind (λ ρ _ → ι == ρ) idp
