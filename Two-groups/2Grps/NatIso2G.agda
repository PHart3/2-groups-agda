{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 #-}

open import lib.Basics
open import lib.FTID
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Semigroup
open import 2SGrpMap

module NatIso2G where

-- properties of natural isos between semigroup morphisms

open WkSGrp {{...}}
open WkSGrpNatIso

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {μ₁ μ₂ : WkSGrpWkHom {{η₁}} {{η₂}}} where

  =WkSGrpNatIso : (ι ρ : WkSGrpNatIso μ₁ μ₂) → Type (lmax i j)
  =WkSGrpNatIso ι ρ = Σ (θ ι == θ ρ) (λ e → θ-comp ι == θ-comp ρ [ _ ↓ e ])

  ∼WkSGrpNatIso : (ι ρ : WkSGrpNatIso μ₁ μ₂) → Type (lmax i j)
  ∼WkSGrpNatIso ι ρ = θ ι ∼ θ ρ

  module _ {ι ρ : WkSGrpNatIso μ₁ μ₂} where

    =WkSGrpNatIso→ : (ι == ρ) → =WkSGrpNatIso ι ρ
    fst (=WkSGrpNatIso→ idp) = idp
    snd (=WkSGrpNatIso→ idp) = idp

    =WkSGrpNatIso← : =WkSGrpNatIso ι ρ → (ι == ρ)
    =WkSGrpNatIso← (idp , idp) = idp

    =WkSGrpNatIso←→ : (e : ι == ρ) → =WkSGrpNatIso← (=WkSGrpNatIso→ e) == e
    =WkSGrpNatIso←→  idp = idp

    =WkSGrpNatIso→← : (e : =WkSGrpNatIso ι ρ) → =WkSGrpNatIso→ (=WkSGrpNatIso← e) == e
    =WkSGrpNatIso→← (idp , idp) = idp

  module _ {ι ρ : WkSGrpNatIso μ₁ μ₂} where

    =WkSGrpNatIso-econv : (ι == ρ) ≃ =WkSGrpNatIso ι ρ
    =WkSGrpNatIso-econv = 
      equiv
        =WkSGrpNatIso→
        =WkSGrpNatIso←
        =WkSGrpNatIso→←
        =WkSGrpNatIso←→ 

    =WkSGrpNatIso∼ : =WkSGrpNatIso ι ρ ≃ (θ ι ∼ θ ρ)
    =WkSGrpNatIso∼ = 
      equiv
        (λ (e₁ , e₂) x → app= e₁ x)
        (λ H → (λ= H) , prop-has-all-paths-↓ {{Π-level-instance}} )
        (λ b → λ= (app=-β b))
        λ a → pair= (! (λ=-η (fst a))) (prop-has-all-paths-↓ {{↓-level}})

  abstract
    natiso∼-contr : (ι : WkSGrpNatIso μ₁ μ₂) → is-contr (Σ (WkSGrpNatIso μ₁ μ₂) (λ ρ → θ ι ∼ θ ρ))
    natiso∼-contr ι = equiv-preserves-level aux
      where
        aux :
          Σ (WkSGrpNatIso μ₁ μ₂) (λ ρ → ι == ρ)
          ≃
          Σ (WkSGrpNatIso μ₁ μ₂) (λ ρ → θ ι ∼ θ ρ)
        aux = Σ-emap-r (λ _ → =WkSGrpNatIso∼ ∘e =WkSGrpNatIso-econv)

  module _ {ι : WkSGrpNatIso μ₁ μ₂} where

    natiso∼-ind : ∀ {k} (P : (ρ : WkSGrpNatIso μ₁ μ₂) → θ ι ∼ θ ρ → Type k)
      → P ι (λ z → idp) → {ρ : WkSGrpNatIso μ₁ μ₂} (p : θ ι ∼ θ ρ) → P ρ p
    natiso∼-ind P = ID-ind-map P (natiso∼-contr ι)

    -- SIP for natural isos
    natiso∼-to-== : {ρ : WkSGrpNatIso μ₁ μ₂} → θ ι ∼ θ ρ → ι == ρ
    natiso∼-to-== = natiso∼-ind (λ ρ _ → ι == ρ) idp

    natiso∼-to-==-β : natiso∼-to-== (λ _ → idp) == idp
    natiso∼-to-==-β = ID-ind-map-β (λ ρ _ → ι == ρ) (natiso∼-contr ι) idp

  natiso∼-to-==-! : {ι ρ : WkSGrpNatIso μ₁ μ₂} (H : θ ι ∼ θ ρ)
    → ! (natiso∼-to-== {ι = ι} H) == natiso∼-to-== {ι = ρ} (! ∘ H)
  natiso∼-to-==-! =
    natiso∼-ind (λ ρ H → ! (natiso∼-to-== H) == natiso∼-to-== {ι = ρ} (! ∘ H))
      (ap ! natiso∼-to-==-β ∙ ! natiso∼-to-==-β)

  natiso∼-to-==-∙ : {ι ρ κ : WkSGrpNatIso μ₁ μ₂} (H₂ : θ ρ ∼ θ κ) (H₁ : θ ι ∼ θ ρ)
    → natiso∼-to-== {ρ = ρ} H₁ ∙ natiso∼-to-== H₂ == natiso∼-to-== {ι = ι} {ρ = κ} (λ x → H₁ x ∙ H₂ x)
  natiso∼-to-==-∙ {ι} {ρ} = 
    natiso∼-ind {ρ} (λ κ H₂ → (H₁ : θ ι ∼ θ ρ) →
      natiso∼-to-== {ρ = ρ} H₁ ∙ natiso∼-to-== H₂ == natiso∼-to-== {ι = ι} {ρ = κ} (λ x → H₁ x ∙ H₂ x))
      λ H₁ → ap (λ e → natiso∼-to-== H₁ ∙ e) natiso∼-to-==-β ∙ ∙-unit-r _ ∙ ! (ap natiso∼-to-== (λ= (λ x → ∙-unit-r (H₁ x))))

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}} where

  !ʷ-id : (μ : WkSGrpWkHom {{η₁}} {{η₂}}) → !ʷ (natiso-id μ) == natiso-id μ
  !ʷ-id _ = natiso∼-to-== λ x → idp

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {μ : WkSGrpWkHom {{η₁}} {{η₂}}} {G₃ : Type k} {{η₃ : WkSGrp G₃}} where
  
  natiso-whisk-r-id : (ν : WkSGrpWkHom {{η₂}} {{η₃}}) → natiso-whisk-r (natiso-id ν) == natiso-id (ν ∘2Mw μ) 
  natiso-whisk-r-id _ = natiso∼-to-== λ x → idp

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {G₃ : Type k} {{η₃ : WkSGrp G₃}} {μ : WkSGrpWkHom {{η₂}} {{η₃}}} where

  natiso-whisk-l-id : (ν : WkSGrpWkHom {{η₁}} {{η₂}}) → natiso-whisk-l {μ = μ} (natiso-id ν) == natiso-id (μ ∘2Mw ν)
  natiso-whisk-l-id ν = natiso∼-to-== λ x → idp

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {μ₁ μ₂ μ₃ : WkSGrpWkHom {{η₁}} {{η₂}}} where

  abstract
    natiso-∘=∘' : {n₁ : WkSGrpNatIso μ₂ μ₃} (n₂ : WkSGrpNatIso μ₁ μ₂) → n₁ natiso-∘ n₂ == n₁ natiso-∘' n₂
    natiso-∘=∘' {n₁} n₂ = natiso∼-to-== λ x → ∙=∙' (θ n₂ x) (θ n₁ x)
