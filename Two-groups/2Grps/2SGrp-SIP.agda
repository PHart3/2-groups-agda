{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=4 #-}

open import lib.Basics
open import lib.Funext2
open import lib.FTID
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.Pi
open import 2Semigroup

module 2SGrp-SIP where

-- SIP for semigroups

open WkSGrpHom

module _ {i j} {G₁ : Type i} {G₂ : Type j} where

  infix 30 _≃-2sg_
  _≃-2sg_ : WkSGrp G₁ → WkSGrp G₂ → Type (lmax i j)
  η₁ ≃-2sg η₂ = Σ (WkSGrpHom {{η₁}} {{η₂}}) (λ φ → is-equiv (map {{η₁}} {{η₂}} φ)) 

ide2SG : ∀ {i} {G : Type i} (η : WkSGrp G) → η ≃-2sg η
map (fst (ide2SG {G = G} η)) = idf G
str (fst (ide2SG η)) = idf2M {{η}}
snd (ide2SG {G = G} η) = idf-is-equiv G

module _ {i} (G₁ : Type i) (η₁ : WkSGrp G₁) where

  open WkSGrp η₁

  ≃-2sg-contr : is-contr $
    [ ( ( G₂ , _ ) , ( map , _ ) ) ∈ Σ (1 -Type i) (λ ( G₂ , _ ) → G₁ ≃ G₂) ] ×
      [ ( mu₂ , map-comp ) ∈ Σ (G₂ → G₂ → G₂) (λ mu₂ → (x y : G₁) → mu₂ (map x) (map y) == map (mu x y)) ] ×
        (Σ ((x y z : G₂) → mu₂ x (mu₂ y z) == mu₂ (mu₂ x y) z)
          (λ al₂ →
            (x y z : G₁) →
              ! (al₂ (map x) (map y) (map z)) ∙ ap (mu₂ (map x)) (map-comp y z) ∙ map-comp x (mu y z)
                ==
              ap (λ v → mu₂ v (map z)) (map-comp x y) ∙ map-comp (mu x y) z ∙ ! (ap map (al x y z))))
  ≃-2sg-contr = equiv-preserves-level
    ((Σ-contr-red {A = Σ (1 -Type i) (λ (G₂ , _) → G₁ ≃ G₂)} (nType=-contr (G₁ , 1trunc)))⁻¹)
    {{equiv-preserves-level ((Σ-contr-red {A = Σ (G₁ → G₁ → G₁) (λ mu₂ → (x y : G₁) → mu₂ x y == mu x y)}
      (funhom-iter-contr-to (S I) mu))⁻¹)
        {{equiv-preserves-level
          {B = Σ ((x y z : G₁) → mu x (mu y z) == mu (mu x y) z)
            (λ al₂ → (x y z : G₁) → ! (al₂ x y z) ∙ idp == ! (ap (λ v → v) (al x y z)))}
          (choice ∘e Π-emap-r (λ _ → choice) ∘e Π-emap-r (λ _ → Π-emap-r (λ _ → choice)))}}}}
  
  abstract
    2sgrphomΣ-≃ :
      [ ( ( G₂ , _ ) , ( map , _ ) ) ∈ Σ (1 -Type i) (λ ( G₂ , _ ) → G₁ ≃ G₂) ] ×
        [ ( mu₂ , map-comp ) ∈ Σ (G₂ → G₂ → G₂) (λ mu₂ → (x y : G₁) → mu₂ (map x) (map y) == map (mu x y)) ] ×
          (Σ ((x y z : G₂) → mu₂ x (mu₂ y z) == mu₂ (mu₂ x y) z)
            (λ al₂ →
              (x y z : G₁) →
                ! (al₂ (map x) (map y) (map z)) ∙ ap (mu₂ (map x)) (map-comp y z) ∙ map-comp x (mu y z)
                  ==
                ap (λ v → mu₂ v (map z)) (map-comp x y) ∙ map-comp (mu x y) z ∙ ! (ap map (al x y z))))
        ≃
      Σ (Σ (Type i) (λ G₂ → WkSGrp G₂)) (λ (_ , η₂) → η₁ ≃-2sg η₂)
    2sgrphomΣ-≃ =
      equiv
        (λ ((( G₂ , 1trunc₂ ) , φ ) , ( mu₂ , map-comp ) , ( al₂ , map-al )) →
            (G₂ , wksgrp {{1trunc₂}} mu₂ al₂) , (cohsgrphom (fst φ) {{cohsgrphomstr map-comp map-al}} , (snd φ)))
        (λ ((G₂ , wksgrp {{1trunc₂}} mu₂ al₂) , (cohsgrphom φ₁ {{cohsgrphomstr map-comp map-al}} , φ₂)) →
          (( G₂ , 1trunc₂ ) , φ₁ , φ₂ ) , ( mu₂ , map-comp ) , ( al₂ , map-al ))
        (λ _ → idp)
        λ _ → idp

  abstract
    2sgrphom-contr : is-contr (Σ (Σ (Type i) (λ G₂ → WkSGrp G₂)) (λ (_ , η₂) → η₁ ≃-2sg η₂))
    2sgrphom-contr = equiv-preserves-level 2sgrphomΣ-≃ {{≃-2sg-contr}}

module _ {i} {G₁ : Type i} {η₁ : WkSGrp G₁} where

  2sgrphom-ind : ∀ {k} (P : ((_ , η₂) : Σ (Type i) (λ G₂ → WkSGrp G₂)) → η₁ ≃-2sg η₂ → Type k)
    → P (G₁ , η₁) (ide2SG η₁) → {(G₂ , η₂) : Σ (Type i) (λ G₂ → WkSGrp G₂)} (m : η₁ ≃-2sg η₂) → P (G₂ , η₂) m
  2sgrphom-ind P = ID-ind-map P (2sgrphom-contr G₁ η₁)

  2sgrphom-ind-β : ∀ {k} {P : ((_ , η₂) : Σ (Type i) (λ G₂ → WkSGrp G₂)) → η₁ ≃-2sg η₂ → Type k}
    → (r : P (G₁ , η₁) (ide2SG η₁)) → 2sgrphom-ind P r (ide2SG η₁) == r
  2sgrphom-ind-β {P = P} = ID-ind-map-β P (2sgrphom-contr G₁ η₁)

-- induced CohGrp data on a weak semigroup
open import 2Grp
sGrp-≃-to-coh : ∀ {i} {G₁ G₂ : Type i} {η₁ : WkSGrp G₁} {η₂ : WkSGrp G₂} →
  η₁ ≃-2sg η₂ → CohGrp-data (WkSGrp.mu η₁) (WkSGrp.al η₁) → CohGrp-data (WkSGrp.mu η₂) (WkSGrp.al η₂)
sGrp-≃-to-coh {η₁ = η₁} {η₂} = 2sgrphom-ind
  (λ (G , η) _ → CohGrp-data (WkSGrp.mu η₁) (WkSGrp.al η₁) → CohGrp-data (WkSGrp.mu η) (WkSGrp.al η))
  (λ cg → cg) {_ , η₂}
