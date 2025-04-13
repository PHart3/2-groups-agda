{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Semigroup

module 2SGrpMap where

open WkSGrp {{...}}
open WkSGrpNatIso

module _ {i j k l} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k} {G₄ : Type l}
  {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}} {{η₃ : WkSGrp G₃}} {{η₄ : WkSGrp G₄}} where

  assoc-wksgrphom :
    (μ₁ : WkSGrpWkHom {{η₃}} {{η₄}}) (μ₂ : WkSGrpWkHom {{η₂}} {{η₃}}) (μ₃ : WkSGrpWkHom {{η₁}} {{η₂}})
    → WkSGrpNatIso (μ₁ ∘2Mw μ₂ ∘2Mw μ₃) ((μ₁ ∘2Mw μ₂) ∘2Mw μ₃)
  θ (assoc-wksgrphom μ₁ μ₂ μ₃) x = idp
  θ-comp (assoc-wksgrphom μ₁ μ₂ μ₃) x y = =ₛ-out $
    (map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ∙
    ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y))) ◃∙
    ap (λ v → map-wk μ₁ (map-wk μ₂ v)) (map-comp-wk μ₃ x y) ◃∎
      =ₛ₁⟨ 1 & 1 & ap-∘ (map-wk μ₁) (map-wk μ₂) (map-comp-wk μ₃ x y) ⟩
    (map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ∙
    ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y))) ◃∙
    ap (map-wk μ₁) (ap (map-wk μ₂) (map-comp-wk μ₃ x y)) ◃∎
      =ₑ⟨ 0 & 1 &
        (map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ◃∙
        ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y)) ◃∎) % =ₛ-in idp ⟩
    map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ◃∙
    ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y)) ◃∙
    ap (map-wk μ₁) (ap (map-wk μ₂) (map-comp-wk μ₃ x y)) ◃∎
      =ₛ₁⟨ 1 & 2 & ∙-ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y)) _ ⟩
    map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ◃∙
    ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y) ∙
      ap (map-wk μ₂) (map-comp-wk μ₃ x y)) ◃∎
      =ₛ⟨ =ₛ-in (! (∙-unit-r (map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ∙
             ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y) ∙
             ap (map-wk μ₂) (map-comp-wk μ₃ x y))))) ⟩
    (map-comp-wk μ₁ (map-wk μ₂ (map-wk μ₃ x)) (map-wk μ₂ (map-wk μ₃ y)) ∙
    ap (map-wk μ₁) (map-comp-wk μ₂ (map-wk μ₃ x) (map-wk μ₃ y) ∙
    ap (map-wk μ₂) (map-comp-wk μ₃ x y))) ◃∙
    idp ◃∎ ∎ₛ

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}} where

  !ʷ : {μ₁ μ₂ : WkSGrpWkHom {{η₁}} {{η₂}}} (γ : WkSGrpNatIso μ₁ μ₂) → WkSGrpNatIso μ₂ μ₁
  θ (!ʷ γ) x = ! (θ γ x)
  θ-comp (!ʷ γ) x y = aux {p₁ = θ γ x} (θ-comp γ x y)
    where
      aux : {x₁ x₂ x₃ x₄ x₅ x₆ : G₂} {p₁ : x₁ == x₂} {p₂ : x₃ == x₄}
        {p₃ : mu x₁ x₃ == x₅} {p₄ : x₅ == x₆} {p₀ : mu x₂ x₄ == x₆}
        → p₀ == ! (ap2 mu p₁ p₂) ∙ p₃ ∙ p₄
        → p₃ == ! (ap2 mu (! p₁) (! p₂)) ∙ p₀ ∙ ! p₄
      aux {p₁ = idp} {p₂ = idp} {p₃ = idp} {p₄ = idp} idp = idp

  unit-wksgrphom-l : (μ : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso μ (idf2Mw {{η₂}} ∘2Mw μ)
  θ (unit-wksgrphom-l μ) x = idp
  θ-comp (unit-wksgrphom-l μ) x y = ap-idf (map-comp-wk μ x y) ∙ ! (∙-unit-r (map-comp-wk μ x y))

  unit-wksgrphom-r : (μ : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso μ (μ ∘2Mw idf2Mw {{η₁}})
  θ (unit-wksgrphom-r μ) x = idp
  θ-comp (unit-wksgrphom-r μ) x y = idp

  unit-wksgrphom : (μ : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso (idf2Mw {{η₂}} ∘2Mw μ) μ
  unit-wksgrphom μ = !ʷ (unit-wksgrphom-l μ)

  module _ {μ : WkSGrpWkHom {{η₁}} {{η₂}}} where

    natiso-contr-aux :
      is-contr (Σ (Σ (G₁ → G₂) (λ f → map-wk μ ∼ f))
        (λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
          (λ c → ((x , y) : G₁ × G₁) →
            c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y))))
    natiso-contr-aux = equiv-preserves-level (
      (Σ-contr-red
        {P = λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
          (λ c → ((x , y) : G₁ × G₁) →
            c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y))}
        (funhom-contr {f = map-wk μ}))⁻¹ )
      {{equiv-preserves-level
        ((Σ-emap-r (λ c → Π-emap-r (λ (x , y) → post∙-equiv (! (∙-unit-r (map-comp-wk μ x y)))) ∘e app=-equiv)))
        {{pathto-is-contr (uncurry (map-comp-wk μ))}}}}

    abstract
      natiso-contr : is-contr (Σ (WkSGrpWkHom {{η₁}} {{η₂}}) (λ ν → WkSGrpNatIso μ ν))
      natiso-contr = equiv-preserves-level aux {{natiso-contr-aux}}
        where
          aux :
            Σ (Σ (G₁ → G₂) (λ f → map-wk μ ∼ f))
              (λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
                (λ c → ((x , y) : G₁ × G₁) →
                  c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y)))
            ≃
            Σ (WkSGrpWkHom {{η₁}} {{η₂}}) (λ ν → WkSGrpNatIso μ ν)
          aux =
            equiv
              (λ ((f , H) , (q , c)) → (wksgrphom f (curry q)) , (cohgrpnatiso H (λ x y → c (x , y))))
              (λ (ν , ρ) → ((map-wk ν) , (θ ρ)) , ((λ (x , y) → map-comp-wk ν x y) , (λ (x , y) → θ-comp ρ x y)))
              (λ b → idp)
              λ a → idp

    natiso-ind : ∀ {k} (P : (ν : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso μ ν →  Type k)
      → P μ (natiso-id μ) → (ν : WkSGrpWkHom {{η₁}} {{η₂}}) (p : WkSGrpNatIso μ ν) → P ν p
    natiso-ind P r ν p = ID-ind-map P natiso-contr r {ν} p

    natiso-ind-β : ∀ {k} (P : (ν : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso μ ν →  Type k)
      → (r : P μ (natiso-id μ)) → natiso-ind P r μ (natiso-id μ) == r
    natiso-ind-β P = ID-ind-map-β P natiso-contr 

    natiso-to-== : {ν : WkSGrpWkHom {{η₁}} {{η₂}}} → WkSGrpNatIso μ ν → μ == ν
    natiso-to-== {ν} = natiso-ind (λ δ _ → μ == δ) idp ν

  -- equational reasoning for nat isos.

  infixr 10 _=⟦_⟧_
  infix  15 _∎ₙ

  _=⟦_⟧_ : (μ₁ : WkSGrpWkHom {{η₁}} {{η₂}}) {μ₂ μ₃ : _}
    → WkSGrpNatIso μ₁ μ₂ → WkSGrpNatIso μ₂ μ₃ → WkSGrpNatIso μ₁ μ₃
  _=⟦_⟧_ μ₁ {μ₂} {μ₃} τ = natiso-ind (λ ν τ → WkSGrpNatIso ν μ₃ → WkSGrpNatIso μ₁ μ₃) (λ x → x) μ₂ τ

  _∎ₙ : (μ : WkSGrpWkHom {{η₁}} {{η₂}}) → WkSGrpNatIso μ μ
  μ ∎ₙ = natiso-id μ

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {μ : WkSGrpWkHom {{η₁}} {{η₂}}} {G₃ : Type k} {{η₃ : WkSGrp G₃}} where

  natiso-whisk-r : {ν₁ ν₂ : WkSGrpWkHom {{η₂}} {{η₃}}} (τ : WkSGrpNatIso ν₁ ν₂)
    → WkSGrpNatIso (ν₁ ∘2Mw μ) (ν₂ ∘2Mw μ)
  θ (natiso-whisk-r {ν₁} {ν₂} τ) x = θ τ (map-wk μ x)
  θ-comp (natiso-whisk-r {ν₁} {ν₂} τ) x y =
    natiso-ind
      (λ ν τ →
        map-comp-wk ν (map-wk μ x) (map-wk μ y) ∙
        ap (map-wk ν) (map-comp-wk μ x y)
          ==
        ! (ap2 mu (θ τ (map-wk μ x)) (θ τ (map-wk μ y))) ∙
        (map-comp-wk ν₁ (map-wk μ x) (map-wk μ y) ∙
        ap (map-wk ν₁) (map-comp-wk μ x y)) ∙
        θ τ (map-wk μ (mu x y)))
      (! (∙-unit-r _)) ν₂ τ

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}}
  {G₃ : Type k} {{η₃ : WkSGrp G₃}} {μ : WkSGrpWkHom {{η₂}} {{η₃}}} where

  natiso-whisk-l : {ν₁ ν₂ : WkSGrpWkHom {{η₁}} {{η₂}}} (τ : WkSGrpNatIso ν₁ ν₂)
    → WkSGrpNatIso (μ ∘2Mw ν₁) (μ ∘2Mw ν₂)
  θ (natiso-whisk-l {ν₁} {ν₂} τ) x = ap (map-wk μ) (θ τ x)
  θ-comp (natiso-whisk-l {ν₁} {ν₂} τ) x y =
    natiso-ind
      (λ ν τ →
        map-comp-wk μ (map-wk ν x) (map-wk ν y) ∙
        ap (map-wk μ) (map-comp-wk ν x y)
          ==
        ! (ap2 mu (ap (map-wk μ) (θ τ x)) (ap (map-wk μ) (θ τ y))) ∙
        (map-comp-wk μ (map-wk ν₁ x) (map-wk ν₁ y) ∙
        ap (map-wk μ) (map-comp-wk ν₁ x y)) ∙
        ap (map-wk μ) (θ τ (mu x y)))
      (! (∙-unit-r _)) ν₂ τ

-- composite of triangles
module _ {i j k l} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k} {G₄ : Type l}
  {{η₁ : WkSGrp G₁}} {{η₂ : WkSGrp G₂}} {{η₃ : WkSGrp G₃}} {{η₄ : WkSGrp G₄}} where

  natiso-tri-∘ : {μ₁ : WkSGrpWkHom {{η₁}} {{η₂}}} {μ₂ : WkSGrpWkHom {{η₁}} {{η₃}}} {μ₃ : WkSGrpWkHom {{η₁}} {{η₄}}}
    {ω₁ : WkSGrpWkHom {{η₂}} {{η₃}}} {ω₂ : WkSGrpWkHom {{η₃}} {{η₄}}}
    → WkSGrpNatIso (ω₁ ∘2Mw μ₁) μ₂ → WkSGrpNatIso (ω₂ ∘2Mw μ₂) μ₃ → WkSGrpNatIso (ω₂ ∘2Mw ω₁ ∘2Mw μ₁) μ₃
  natiso-tri-∘ {μ₁} {μ₂} {μ₃} {ω₁} {ω₂} τ = 
    natiso-ind (λ ν τ → WkSGrpNatIso (ω₂ ∘2Mw ν) μ₃ → WkSGrpNatIso (ω₂ ∘2Mw ω₁ ∘2Mw μ₁) μ₃) (λ x → x) μ₂ τ

