{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma

module 2MagMap where

open WkMag {{...}}
open WkMagNatIso

module _ {i j k l} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k} {G₄ : Type l}
  {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} {{η₃ : WkMag G₃}} {{η₄ : WkMag G₄}} where

  assoc-wkmaghom :
    (μ₁ : WkMagWkHom {{η₃}} {{η₄}}) (μ₂ : WkMagWkHom {{η₂}} {{η₃}}) (μ₃ : WkMagWkHom {{η₁}} {{η₂}})
    → WkMagNatIso (μ₁ ∘2Mw μ₂ ∘2Mw μ₃) ((μ₁ ∘2Mw μ₂) ∘2Mw μ₃)
  θ (assoc-wkmaghom μ₁ μ₂ μ₃) x = idp
  θ-comp (assoc-wkmaghom μ₁ μ₂ μ₃) x y = =ₛ-out $
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

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} where

  unit-wkmaghom : (μ : WkMagWkHom {{η₁}} {{η₂}}) → WkMagNatIso (idf2Mw {{η₂}} ∘2Mw μ) μ
  θ (unit-wkmaghom μ) x = idp
  θ-comp (unit-wkmaghom μ) x y =
    ! (ap (λ p → p ∙ idp) (ap-idf (map-comp-wk μ x y)) ∙ ∙-unit-r (map-comp-wk μ x y))

  module _ {μ : WkMagWkHom {{η₁}} {{η₂}}} where

    natiso-contr-aux :
      is-contr (Σ (Σ (G₁ → G₂) (λ f → map-wk μ ∼ f))
        (λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
          (λ c → ((x , y) : G₁ × G₁) →
            c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y))))
    natiso-contr-aux = equiv-preserves-level (
      (Σ-contr-red {P = λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
        (λ c → ((x , y) : G₁ × G₁) →
          c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y))}
        (funhom-contr {f = map-wk μ}))⁻¹ )
      {{equiv-preserves-level ((Σ-emap-r (λ c → Π-emap-r (λ (x , y)
        → post∙-equiv (! (∙-unit-r (map-comp-wk μ x y)))) ∘e app=-equiv)))
        {{pathto-is-contr (uncurry (map-comp-wk μ))}}}}

    natiso-contr : is-contr (Σ (WkMagWkHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso μ ν))
    natiso-contr = equiv-preserves-level aux {{natiso-contr-aux}}
      where
        aux :
          (Σ (Σ (G₁ → G₂) (λ f → map-wk μ ∼ f))
            (λ (f , H) → Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
              (λ c → ((x , y) : G₁ × G₁) →
                c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk μ) (x , y) ∙ H (mu x y))))
          ≃
          Σ (WkMagWkHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso μ ν)
        aux =
          equiv
            (λ ((f , H) , (q , c)) → (wkmaghom f (curry q)) , (cohgrpnatiso H (λ x y → c (x , y))))
            (λ (ν , ρ) → ((map-wk ν) , (θ ρ)) , ((λ (x , y) → map-comp-wk ν x y) , (λ (x , y) → θ-comp ρ x y)))
            (λ b → idp)
            λ a → idp

    natiso-cent : (r : Σ (WkMagWkHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso μ ν))
      → (μ , natiso-id μ) == r
    natiso-cent r = contr-path natiso-contr r

    natiso-ind : ∀ {k} (P : (ν : WkMagWkHom {{η₁}} {{η₂}}) → WkMagNatIso μ ν →  Type k)
      → P μ (natiso-id μ) → (ν : WkMagWkHom {{η₁}} {{η₂}}) (p : WkMagNatIso μ ν) → P ν p
    natiso-ind P r ν p = ind (ID-ind {P = P} natiso-cent) r ν p

  -- equational reasoning for nat isos.

  infixr 10 _=⟦_⟧_
  infix  15 _∎ₙ

  _=⟦_⟧_ : (μ₁ : WkMagWkHom {{η₁}} {{η₂}}) {μ₂ μ₃ : _}
    → WkMagNatIso μ₁ μ₂ → WkMagNatIso μ₂ μ₃ → WkMagNatIso μ₁ μ₃
  _=⟦_⟧_ μ₁ {μ₂} {μ₃} τ = natiso-ind (λ ν τ → WkMagNatIso ν μ₃ → WkMagNatIso μ₁ μ₃) (λ x → x) μ₂ τ

  _∎ₙ : (μ : WkMagWkHom {{η₁}} {{η₂}}) → WkMagNatIso μ μ
  μ ∎ₙ = natiso-id μ

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}}
  {μ : WkMagWkHom {{η₁}} {{η₂}}} {G₃ : Type k} {{η₃ : WkMag G₃}} where

  natiso-whisk : {ν₁ ν₂ : WkMagWkHom {{η₂}} {{η₃}}} (τ : WkMagNatIso ν₁ ν₂)
    → WkMagNatIso (ν₁ ∘2Mw μ) (ν₂ ∘2Mw μ)
  natiso-whisk {ν₁} {v₂} τ =
    natiso-ind (λ ν τ → WkMagNatIso (ν₁ ∘2Mw μ) (ν ∘2Mw μ)) (natiso-id _) v₂ τ

-- composite of triangles
module _ {i j k l} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k} {G₄ : Type l}
  {{η₁ : WkMag G₁}} {{η₂ : WkMag G₂}} {{η₃ : WkMag G₃}} {{η₄ : WkMag G₄}} where

  natiso-tri-∘ : {μ₁ : WkMagWkHom {{η₁}} {{η₂}}} {μ₂ : WkMagWkHom {{η₁}} {{η₃}}} {μ₃ : WkMagWkHom {{η₁}} {{η₄}}}
    {ω₁ : WkMagWkHom {{η₂}} {{η₃}}} {ω₂ : WkMagWkHom {{η₃}} {{η₄}}}
    → WkMagNatIso (ω₁ ∘2Mw μ₁) μ₂ → WkMagNatIso (ω₂ ∘2Mw μ₂) μ₃ → WkMagNatIso (ω₂ ∘2Mw ω₁ ∘2Mw μ₁) μ₃
  natiso-tri-∘ {μ₁} {μ₂} {μ₃} {ω₁} {ω₂} τ = 
    natiso-ind (λ ν τ → WkMagNatIso (ω₂ ∘2Mw ν) μ₃ → WkMagNatIso (ω₂ ∘2Mw ω₁ ∘2Mw μ₁) μ₃) (λ x → x) μ₂ τ

