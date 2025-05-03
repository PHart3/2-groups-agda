{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.NType2
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import Bicategory

module Bicat-iso-aux where

open BicatStr

module _ {i j} {B₀ : Type i} (ξB : BicatStr j B₀) where

  tot-iso-bc : Type (lmax (lsucc i) (lsucc j))
  tot-iso-bc =
    [ (C₀ , F₀ , _) ∈ Σ (Type i) (λ C₀ → B₀ ≃ C₀) ] ×
      [ (homC , F₁) ∈ Σ (C₀ × C₀ → Type j) (λ homC → ((a , b) : B₀ × B₀) → hom ξB a b ≃ homC (F₀ a , F₀ b)) ] ×
        [ (id₁C , F-id) ∈ Σ ((a : C₀) → homC (a , a)) (λ id₁C → ∀ a → (–> (F₁ (a , a)) (id₁ ξB a) == id₁C (F₀ a))) ] ×
          [ (◻-C , F-◻) ∈  Σ ((((a , b , c) , _) : Σ (C₀ × C₀ × C₀) (λ (a , b , c) → homC (b , c) × homC (a , b))) → homC (a , c))
            (λ ◻-C → (((a , b , c) , (g , f)) : Σ (B₀ × B₀ × B₀) (λ (a , b , c) →  hom ξB b c × hom ξB a b)) →
              –> (F₁ (a , c)) (⟦ ξB ⟧ g ◻ f) == ◻-C (_ , (–> (F₁ (b , c)) g ,  –> (F₁ (a , b)) f))) ] ×
            [ (ρC , _) ∈ Σ ((((a , b) , f) : Σ (C₀ × C₀) (λ (a , b) → homC (a , b))) → f == ◻-C (_ , (f , id₁C a)))
              (λ ρC → (((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom ξB a b)) →
                ap (–> (F₁ (a , b))) (ρ ξB f) ∙ F-◻ (_ , (f , id₁ ξB a)) ∙ ap (λ m → ◻-C (_ , (–> (F₁ (a , b)) f , m))) (F-id a)
                  ==
                ρC (_ , –> (F₁ (a , b)) f)) ] ×
              [ (lambC , _) ∈  Σ ((((a , b) , f) : Σ (C₀ × C₀) (λ (a , b) → homC (a , b))) → f == ◻-C (_ , (id₁C b , f)))
                (λ lambC → (((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom ξB a b)) →
                  ap (–> (F₁ (a , b))) (lamb ξB f) ∙ F-◻ (_ , (id₁ ξB b , f)) ∙ ap (λ m → ◻-C (_ , (m , –> (F₁ (a , b)) f))) (F-id b)
                    ==
                  lambC (_ , –> (F₁ (a , b)) f)) ] ×
                 [ (αC , _) ∈ Σ ((((a , b , c , d) , (h , g , f)) : Σ (C₀ × C₀ × C₀ × C₀)
                   (λ (a , b , c , d) → homC (c , d) × homC (b , c) × homC (a , b)))
                     → ◻-C (_ , (h , ◻-C (_ , (g , f)))) == ◻-C (_ , (◻-C (_ , (h , g)) , f)))
                     (λ αC → (((a , b , c , d) , (h , g , f)) : Σ (B₀ × B₀ × B₀ × B₀)
                       (λ (a , b , c , d) → hom ξB c d × hom ξB b c × hom ξB a b)) →
                         ! (ap (λ m → ◻-C (_ , (–> (F₁ (c , d)) h , m))) (F-◻ (_ , (g , f)))) ∙
                         ! (F-◻ (_ , (h , ⟦ ξB ⟧ g ◻ f))) ∙
                         ap (–> (F₁ (a , d))) (α ξB h g f) ∙
                         F-◻ (_ , (⟦ ξB ⟧ h ◻ g , f)) ∙
                         ap (λ m → ◻-C (_ , (m , –> (F₁ (a , b)) f))) (F-◻ (_ , (h , g)))
                           ==
                         αC (_ , (–> (F₁ (c , d)) h , –> (F₁ (b , c)) g , –> (F₁ (a , b)) f))) ] ×
                   [ triC ∈
                     ((((a , b , c) , (f , g)) : Σ (C₀ × C₀ × C₀)
                       (λ (a , b , c) → homC (a , b) × homC (b , c))) →
                         αC (_ , (g , (id₁C b) , f))
                           ==
                         ! (ap (λ m → ◻-C (_ , (g , m))) (lambC (_ , f))) ∙ ap (λ m → ◻-C (_ , (m , f))) (ρC (_ , g))) ] ×
                     [ pentC ∈
                       ((((a , b , c , d , e) , (f , g , h , i)) : Σ (C₀ × C₀ × C₀ × C₀ × C₀)
                         (λ (a , b , c , d , e) → homC (a , b) × homC (b , c) × homC (c , d) × homC (d , e))) →
                           αC (_ , (i , h , ◻-C (_ , (g , f)))) ∙ αC (_ , ((◻-C (_ , (i , h))) , g , f))
                             ==
                           ap (λ m → ◻-C (_ , (i , m))) (αC (_ , (h , g , f))) ∙
                           αC (_ , (i , ◻-C (_ , (h , g)) , f)) ∙
                           ap (λ m → ◻-C (_ , (m , f))) (αC (_ , (i , h , g)))) ] ×
                       ({a b : C₀} → has-level 1 (homC (a , b)))

  abstract
    bc-contr-aux : is-contr tot-iso-bc
    bc-contr-aux = equiv-preserves-level ((Σ-contr-red ≃-tot-contr)⁻¹)
      {{equiv-preserves-level ((Σ-contr-red ≃-∼-tot-contr)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red (funhom-contr {f = id₁ ξB}))⁻¹)
          {{equiv-preserves-level ((Σ-contr-red (funhom-contr {f = λ (_ , (g , f)) → ⟦ ξB ⟧ g ◻ f}))⁻¹)
            {{equiv-preserves-level ((Σ-contr-red (funhom-contr-∼ {f = λ (_ , f) → ap (λ v → v) (ρ ξB f) ∙ idp}
              (λ (_ , f) → ap-idf-idp (ρ ξB f))))⁻¹)
              {{equiv-preserves-level ((Σ-contr-red (funhom-contr-∼ {f = λ (_ , f) → ap (λ v → v) (lamb ξB f) ∙ idp}
                (λ (_ , f) → ap-idf-idp (lamb ξB f))))⁻¹)
                {{equiv-preserves-level ((Σ-contr-red {A =
                  Σ ((((a , b , c , d) , (h , g , f)) : Σ (B₀ × B₀ × B₀ × B₀)
                   (λ (a , b , c , d) → hom ξB c d × hom ξB b c × hom ξB a b))
                     → ⟦ ξB ⟧ h ◻ (⟦ ξB ⟧ g ◻ f) == ⟦ ξB ⟧ (⟦ ξB ⟧ h ◻ g) ◻ f)
                     (λ αC → ((_ , (h , g , f)) : Σ (B₀ × B₀ × B₀ × B₀)
                       (λ (a , b , c , d) → hom ξB c d × hom ξB b c × hom ξB a b)) →
                         ap (λ v → v) (α ξB h g f) ∙ idp
                           ==
                         αC (_ , (h , g , f)))}
                  (funhom-contr-∼ {f = λ (_ , (h , g , f)) → ap (λ v → v) (α ξB h g f) ∙ idp}
                    (λ (_ , (h , g , f)) → ap-idf-idp (α ξB h g f))))⁻¹)
                  {{inhab-prop-is-contr
                    ((λ (_ , (f , g)) → tri-bc ξB f g) ,
                    (λ (_ , (f , g , h , i)) → pent-bc ξB f g h i) ,
                    (λ {a} {b} → hom-trunc ξB {a} {b}))
                    {{Σ-level-instance {{Π-level-instance}}
                    {{Σ-level-instance {{Π-level-instance}}}}}}}}}}}}}}}}}}}}
