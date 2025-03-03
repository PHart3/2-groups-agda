{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import 2Magma
open import 2Grp
open import Delooping
open import KFunctor
open import KFunctor-idf
open import KFunctor-comp
open import apK

module KFunctor-comp-runit-aux2 where

module KFCRU2 {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}}
  {f : G₁ → G₂} (σ : WkMagHomStr f) (x : G₁) where

  open import KFunctor-comp-runit-defs σ x
  
  private
    κ = cohmaghom f {{σ}} ∘2Mσ cohmaghom (idf G₁) {{idf2G}}

  abstract
    KFunc-runit-coher1 : Λ₁ =ₛ Λ₂
    KFunc-runit-coher1 =
      Λ₁
        =ₑ⟨ 5 & 2 & idp ◃∎ % ap-seq-=ₛ (λ q → q) (=ₛ-in (∘-ap-ap-∘-inv (K₂-map σ) (K₂-map idf2G) (loop G₁ x))) ⟩
      _
        =ₛ₁⟨ 4 & 3 & ap2 _∙_ (ap-idf (! (ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G x)))) idp ∙ !-inv-l (ap (ap (K₂-map σ)) (K₂-map-β-pts idf2G x)) ⟩
      Λ₂ ∎ₛ

    KFunc-runit-coher2 :
      Λ₂
        =ₛ
      idp ◃∙
      idp ◃∙
      ap (ap (K₂-map σ)) (! (ap-idf (loop G₁ x))) ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ) (λ z → z) (loop G₁ x))) ◃∙
      idp ◃∙
      idp ◃∎
    KFunc-runit-coher2 =
      Λ₂
        =ₛ₁⟨ 1 & 2 &
          ap2 _∙_ idp (ap-idf (K₂-map-β-pts κ x)) ∙ !-inv-l (K₂-map-β-pts κ x) ⟩
      _
        =ₛ₁⟨ 0 & 3 & ap2 _∙_ idp (ap-idf (! (K₂-map-β-pts σ x))) ∙ !-inv-r (K₂-map-β-pts σ x) ⟩
      idp ◃∙
      idp ◃∙
      ap (ap (K₂-map σ)) (! (ap-idf (loop G₁ x))) ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ) (λ z → z) (loop G₁ x))) ◃∙
      idp ◃∙
      idp ◃∎ ∎ₛ

    KFunc-runit-coher3 : {b : K₂ G₁ η₁} (p : b == base G₁) →
      idp ◃∙
      idp ◃∙
      ap (ap (K₂-map σ)) (! (ap-idf p)) ◃∙
      idp ◃∙
      ap (λ q → q) (ap (λ q → q) (∘-ap (K₂-map σ) (λ z → z) p)) ◃∙
      idp ◃∙
      idp ◃∎
        =ₛ
      hmtpy-nat-∙' (λ z → idp) p ◃∎
    KFunc-runit-coher3 idp = =ₛ-in idp 
