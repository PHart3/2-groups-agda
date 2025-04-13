{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=5 --lossy-unification #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Semigroup
open import 2SGrpMap
open import 2Grp
open import Hmtpy2Grp
open import KFunctor
open import K-hom-ind
open import KFunctor-comp
open import Delooping
open import LoopFunctor-ap

module LoopK-ptr-comp where

module _ {i j k} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}
  (m₁@(cohgrphom f₁ {{σ₁}}) : CohGrpHom {{η₁}} {{η₂}}) (m₂@(cohgrphom f₂ {{σ₂}}) : CohGrpHom {{η₂}} {{η₃}})
  (x : G₁) where

  private
    τ = Ω-fmap-ap (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ∙ ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)
    ν =
      λ v →
        K₂-map-β-pts (m₂ ∘2Gσ m₁) v ∙
        ! (K₂-map-β-pts σ₂ (f₁ v)) ∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ v)) ∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ v)
    Λ =
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      K₂-map-β-pts (m₂ ∘2Gσ m₁) x ◃∙
      ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
      ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∙
      ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
      ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∎

  module LKC-aux where

    abstract
      LoopK-∘-aux : Λ =ₛ idp ◃∎
      LoopK-∘-aux =
        Λ
          =ₛ₁⟨ 0 & 2 & !-inv-l (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ⟩
        idp ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∙
        ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
        ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
        ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
        K₂-map-β-pts σ₂ (f₁ x) ◃∎
          =ₛ₁⟨ 3 & 2 & ∘-ap-ap-∘-inv (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ⟩
        idp ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
        ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∙
        idp ◃∙
        ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
        K₂-map-β-pts σ₂ (f₁ x) ◃∎
          =ₛ₁⟨ 2 & 3 & !-inv-l (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ⟩
        idp ◃∙
        ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
        idp ◃∙
        K₂-map-β-pts σ₂ (f₁ x) ◃∎
          =ₛ₁⟨ !-inv-l (K₂-map-β-pts σ₂ (f₁ x)) ⟩
        idp ◃∎ ∎ₛ

  open LKC-aux

  abstract
    LoopK-∘ :
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      (WkSGrpNatIso.θ (Loop2Grp-map-ap (K₂-map-∘ σ₁ σ₂)) (loop G₁ x) ∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∙
      idp ◃∎
        =ₛ
      idp ◃∎
    LoopK-∘ =
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      (WkSGrpNatIso.θ (Loop2Grp-map-ap (K₂-map-∘ σ₁ σ₂)) (loop G₁ x) ∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 1 & ap (λ p → p ∙ ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)) (Loop2Grp-map-ap-fst (K₂-map-∘ σ₁ σ₂) (loop G₁ x)) ⟩
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      (Ω-fmap-ap (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∙
      idp ◃∎
        =ₛ₁⟨ 3 & 2 & ∙-unit-r (K₂-map-β-pts σ₂ (f₁ x)) ⟩
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      (Ω-fmap-ap (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x)) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∎
        =ₑ⟨ 1 & 1 & (Ω-fmap-ap (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ◃∙ ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∎) % =ₛ-in (idp {a = τ}) ⟩
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      Ω-fmap-ap (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ◃∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∎
        =ₛ⟨ 1 & 1 & Ω-fmap-ap-hnat (K₂-map-∘ σ₁ σ₂) (loop G₁ x) ⟩
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      idp ◃∙
      ap (λ q → q) (hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ σ₂)) (loop G₁ x)) ◃∙
      idp ◃∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∎
        =ₛ₁⟨ 1 & 3 &
          ∙-unit-r (ap (λ q → q) (hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ σ₂)) (loop G₁ x))) ∙ ap-idf (hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ σ₂)) (loop G₁ x)) ⟩
      ! (K₂-map-β-pts (m₂ ∘2Gσ m₁) x) ◃∙
      hmtpy-nat-∙' (fst (K₂-map-∘ σ₁ σ₂)) (loop G₁ x) ◃∙
      ap-∘ (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∙
      ap (Ω-fmap (K₂-map⊙ σ₂)) (K₂-map-β-pts σ₁ x) ◃∙
      K₂-map-β-pts σ₂ (f₁ x) ◃∎
        =ₑ⟨ 1 & 1 &
          (K₂-map-β-pts (m₂ ∘2Gσ m₁) x ◃∙
          ! (K₂-map-β-pts σ₂ (f₁ x)) ◃∙
          ! (ap (ap (K₂-map σ₂)) (K₂-map-β-pts σ₁ x)) ◃∙
          ∘-ap (K₂-map σ₂) (K₂-map σ₁) (loop G₁ x) ◃∎) %
          =ₛ-in (K₂-∼-ind-β (map₁-∘ σ₁ σ₂) (map₂-∘ σ₁ σ₂) idp ν _ x) ⟩
      Λ
        =ₛ⟨ LoopK-∘-aux ⟩
      idp ◃∎ ∎ₛ
