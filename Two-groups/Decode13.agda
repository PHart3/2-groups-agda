{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.LoopSpace
open import 2Grp
open import Codes
open import Decode12

module Decode13 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open import Delooping G

  module _ (z : G) (p₁ p₂ p₃ : base == base) where

    long-aux3 : {e₁ e₂ : G == G} 
      (α₁ : ap fst (ap codes p₁) == e₁) (α₂ : ap fst (ap codes p₂) == e₂)
      (q₂ : loop (coe e₁ z) ∙ p₂ == loop (coe e₂ (coe e₁ z)))
      (q₃ : p₃ ∙ p₁ == loop (coe e₁ z))
      →
      ! (ap loop (transp-∙ p₁ p₂ z)) ∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
        ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ∙
      ap loop (ap (λ q → coe q z) (ap2 _∙_ α₁ α₂)) ∙
      ap loop (coe-∙ e₁ e₂ z) ∙
      ! q₂ ∙
      ! (ap (λ p → p ∙ p₂) q₃) ∙
      ∙-assoc p₃ p₁ p₂ ∙
      ! (transp-cst=idf (p₁ ∙ p₂) p₃)
        ==
      transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
          ap (λ q → coe q z) α₁ ∙ idp))
        (ap loop (transp-coe p₂ (coe e₁ z) ∙
        ap (λ q → coe q (coe e₁ z)) (ap-∘ fst codes p₂) ∙
        ap (λ q → coe q (coe e₁ z)) α₂ ∙ idp) ∙ ! q₂) ∙
      ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ∙
      ap (transport (_==_ base) p₂)
        (ap loop
          (transp-coe p₁ z ∙
          ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
          ap (λ q → coe q z) α₁ ∙ idp)) ∙
      ap (transport (_==_ base) p₂) (! q₃) ∙
      ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
      ! (transp-∙ p₁ p₂ p₃) ∙ idp
    long-aux3 idp idp q₂ q₃ = =ₛ-out (long-aux4 z p₁ p₂ p₃ q₂ q₃)

    long-aux2 : (e₁ e₂ : G ≃ G)
      (α₁ : ap fst (ap codes p₁) == ua e₁) (α₂ : ap fst (ap codes p₂) == ua e₂)
      {g : G} (β₁ : coe (ua e₁) z == g)
      (q₂ : loop g ∙ p₂ == loop (coe (ua e₂) g))
      (q₃ : p₃ ∙ p₁ == loop g)
      → 
      ! (ap loop (transp-∙ p₁ p₂ z)) ∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
        ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ∙
      ap loop (ap (λ q → coe q z) (ap2 _∙_ α₁ α₂)) ∙
      ap loop (coe-∙ (ua e₁) (ua e₂) z) ∙
      ap loop (ap (coe (ua e₂)) β₁) ∙
      ! q₂ ∙
      ! (ap (λ p → p ∙ p₂) q₃) ∙
      ∙-assoc p₃ p₁ p₂ ∙
      ! (transp-cst=idf (p₁ ∙ p₂) p₃)
        ==
      transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
          ap (λ q → coe q z) α₁ ∙ β₁))
        (ap loop (transp-coe p₂ g ∙
        ap (λ q → coe q g) (ap-∘ fst codes p₂) ∙
        ap (λ q → coe q g) α₂ ∙ idp) ∙ ! q₂) ∙
      ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ∙
      ap (transport (_==_ base) p₂)
        (ap loop
          (transp-coe p₁ z ∙
          ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
          ap (λ q → coe q z) α₁ ∙ β₁)) ∙
      ap (transport (_==_ base) p₂) (! q₃) ∙
      ap (transport (_==_ base) p₂) (! (transp-cst=idf p₁ p₃)) ∙
      ! (transp-∙ p₁ p₂ p₃) ∙ idp
    long-aux2 e₁ e₂ α₁ α₂ idp q₂ q₃ = long-aux3 α₁ α₂ q₂ q₃

    long-aux : (e₁ e₂ : G ≃ G)
      (α₁ : ap fst (ap codes p₁) == ua e₁) (α₂ : ap fst (ap codes p₂) == ua e₂)
      (β₁ : coe (ua e₁) z == fst e₁ z) {g : G} (β₂ : coe (ua e₂) (fst e₁ z) == g)
      {t : base == base} (q₁ : p₁ ∙ p₂ == t)
      (q₂ : loop (fst e₁ z) ∙ p₂ == loop g) (q₃ : p₃ ∙ p₁ == loop (fst e₁ z))
      → 
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      ap loop (ap (λ p → transport codes-fst p z) q₁) ◃∙
      transport (λ v → loop (transport codes-fst v z) == loop (coe (ap fst (ap codes v)) z)) q₁
        (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
        ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-Ω-fmap (codes , idp) p₁ p₂)) ∙
          ap (ap fst ∘ ap codes) q₁))) ◃∙
      ap loop (ap (λ q → coe q z) (ap2 _∙_ α₁ α₂)) ◃∙
      ap loop (coe-∙ (ua e₁) (ua e₂) z) ◃∙
      ap loop (ap (coe (ua e₂)) β₁) ◃∙
      ap loop β₂ ◃∙
      ! q₂ ◃∙
      ! (ap (λ p → p ∙ p₂) q₃) ◃∙
      ∙-assoc p₃ p₁ p₂ ◃∙
      ap (λ p → p₃ ∙ p) q₁ ◃∙
      ! (transport
          (λ v → transport (_==_ base) v p₃ == p₃ ∙ v)
          q₁
          (transp-cst=idf (p₁ ∙ p₂) p₃)) ◃∎
        =ₛ
      transport
         (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
         (! (
           transp-coe {B = codes-fst} p₁ z ∙
           ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
           ap (λ q → coe q z) α₁ ∙
           β₁))
         (ap loop
           (
             transp-coe {B = codes-fst} p₂ (fst e₁ z) ∙
             ap (λ q → coe q (fst e₁ z)) (ap-∘ fst codes p₂) ∙
             ap (λ q → coe q (fst e₁ z)) α₂ ∙
             β₂) ∙
           ! q₂) ◃∙
       ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
       ap (transport (λ b → base == b) p₂)
         (ap loop (
           transp-coe {B = codes-fst} p₁ z ∙
           ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙
           ap (λ q → coe q z) α₁ ∙
           β₁)) ◃∙
       ap (transport (λ b → base == b) p₂) (! q₃) ◃∙
       ap (transport (λ b → base == b) p₂) (! (transp-cst=idf p₁ p₃)) ◃∙
       ! (transp-∙ p₁ p₂ p₃) ◃∙
       ap (λ p → transport (λ b → base == b) p p₃) q₁ ◃∎
    long-aux e₁ e₂ α₁ α₂ β₁ idp idp q₂ q₃ = =ₛ-in (long-aux2 e₁ e₂ α₁ α₂ β₁ q₂ q₃)

{-
  p₁ = loop x
  p₂ = loop y
  p₃ = loop z
  α₁ = θ codes-β x
  α₂ = θ codes-β y
  β₁ = coe-β e₁ z
  β₂ = coe-β e₂ (fst e₁ z)
  q₁ = loop-comp x y
  q₂ = loop-comp (fst e₁ z) y
  q₃ = loop-comp z x
  e₁ = ((λ v → mu v x) , mu-post-iso x)
  e₂ = ((λ v → mu v y) , mu-post-iso y)
-}
