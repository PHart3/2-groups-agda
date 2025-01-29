{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2 hiding (linv; rinv)
open import lib.types.LoopSpace
open import 2Magma
open import 2Grp
open import Codes

module Decode11 where

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open CohGrp {{...}}

  open import Delooping G

  long-aux8-aux-aux1 : (z : G) {b : K₂ η} (p₁ : base == b) (p₂ : b == base) →
    ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
      ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
        (ap-∘ fst codes p₂) ∙ idp)) ∙
    ! (ap (λ v → loop (transport codes-fst p₂ v))
      (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ∙
    ! (ap loop (transp-∙ p₁ p₂ z)) ∙
    (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
    ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ∙
    ap loop (ap (λ q → coe q z)
      (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
        ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ∙
    ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z)
      ==
    idp
  long-aux8-aux-aux1 z idp p₂ = aux (transp-coe p₂ z) (ap (λ q → coe q z) (ap-∘ fst codes p₂))
    where
      aux : {x₁ x₂ x₃ : G} (c₁ : x₁ == x₂) (c₂ : x₂ == x₃) →
        ! (ap loop (c₁ ∙ c₂ ∙ idp)) ∙ (ap loop c₁ ∙ ap loop c₂) ∙ idp == idp
      aux idp idp = idp

  long-aux8-aux-aux2 : (z : G) {b : K₂ η} (p₁ : base == base) (p₂ : base == b) →
    ap (λ v → loop v ∙ p₂)
      (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
      =ₛ
    ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
    ap (transport (_==_ base) p₂)
      (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
    idp ◃∙
    transp-cst=idf p₂ (loop (coe (ap fst (ap codes p₁)) z)) ◃∎
  long-aux8-aux-aux2 z p₁ idp =
    ap (λ v → loop v ∙ idp) (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
      =ₛ⟨ ap-∙-unit-r-nat loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ⟩
    ∙-unit-r (loop (transport codes-fst p₁ z)) ◃∙
    ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
    ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      =ₛ₁⟨ 0 & 1 & ! (!-! (∙-unit-r (loop (transport codes-fst p₁ z)))) ⟩
    ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
    ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
    ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      =ₛ₁⟨ 1 & 1 & ap-idf (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ⟩
    ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
    ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
    ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎
      =ₑ⟨ 2 & 1 & (idp ◃∙ ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎) % =ₛ-in idp ⟩
    ! (! (∙-unit-r (loop (transport codes-fst p₁ z)))) ◃∙
    ap (λ v → v) (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
    idp ◃∙
    ! (∙-unit-r (loop (coe (ap fst (ap codes p₁)) z))) ◃∎ ∎ₛ

  module _ (z : G) (p₁ p₂ : base == base)
    (q₂ : loop (coe (ap fst (ap codes p₁)) z) ∙ p₂ == loop (coe (ap fst (ap codes p₂)) (coe (ap fst (ap codes p₁)) z)))
    where

    long-aux8-aux0 =
      ! (transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
        (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂)) ◃∎
        =ₛ⟨ transp-pth!-!◃
              (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)
              (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
                ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
                  (ap-∘ fst codes p₂) ∙ idp) ∙
               ! q₂) ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂) ◃∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∎ ∎ₛ

    long-aux8-aux1 =
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂) ◃∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∎
        =ₛ⟨ 1 & 1 &
          !-∙-!
            (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
              ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
              (ap-∘ fst codes p₂) ∙ idp))
            q₂ ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
        ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
          (ap-∘ fst codes p₂) ∙ idp)) ◃∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∎ ∎ₛ

    long-aux8 :
      ! (transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
        (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂)) ◃∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      idp ◃∎
        =ₛ
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
    long-aux8 = 
      ! (transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
        (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂)) ◃∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      idp ◃∎
        =ₛ⟨ 0 & 1 & long-aux8-aux0 ∙ₛ long-aux8-aux1 ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      ! (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
        ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
          (ap-∘ fst codes p₂) ∙ idp)) ◃∙
      ! (ap (λ v → loop (transport codes-fst p₂ v))
          (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      idp ◃∎
        =ₛ⟨ 2 & 6 & =ₛ-in (long-aux8-aux-aux1 z p₁ p₂) ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      q₂ ◃∙
      idp ◃∙
      ! q₂ ◃∙
      idp ◃∎
        =ₛ₁⟨ 1 & 4 & ap (λ p → q₂ ∙ p) (∙-unit-r (! q₂)) ∙ !-inv-r q₂ ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∙
      idp
        =ₛ₁⟨ ∙-unit-r
               (ap (λ v → loop v ∙ p₂)
                 (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ⟩
      ap (λ v → loop v ∙ p₂)
        (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp) ◃∎
        =ₛ⟨ long-aux8-aux-aux2 z p₁ p₂ ⟩
      ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
      ap (transport (_==_ base) p₂)
        (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      idp ◃∙
      transp-cst=idf p₂ (loop (coe (ap fst (ap codes p₁)) z)) ◃∎ ∎ₛ

    long-aux7 :
      {t : base == base} (q₃ : t == loop (coe (ap fst (ap codes p₁)) z))
      →
      ! (ap loop (transp-∙ p₁ p₂ z)) ◃∙
      (ap loop (transp-coe (p₁ ∙ p₂) z) ∙
      ap loop (ap (λ q → coe q z) (ap-∘ fst codes (p₁ ∙ p₂)))) ◃∙
      ap loop (ap (λ q → coe q z)
        (! ((∙-ap fst (ap codes p₁) (ap codes p₂) ∙
          ap (ap fst) (∙-ap codes p₁ p₂)) ∙ idp))) ◃∙
      ap loop (coe-∙ (ap fst (ap codes p₁)) (ap fst (ap codes p₂)) z) ◃∙
      ! q₂ ◃∙
      ! (ap (λ p → p ∙ p₂) q₃) ◃∎
        =ₛ
      transport (λ v → loop (transport codes-fst p₂ v) == loop v ∙ p₂)
        (! (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp))
        (ap loop (transp-coe p₂ (coe (ap fst (ap codes p₁)) z) ∙
          ap (λ q → coe q (coe (ap fst (ap codes p₁)) z))
            (ap-∘ fst codes p₂) ∙ idp) ∙
         ! q₂) ◃∙
      ! (transp-cst=idf p₂ (loop (transport codes-fst p₁ z))) ◃∙
      ap (transport (_==_ base) p₂)
        (ap loop (transp-coe p₁ z ∙ ap (λ q → coe q z) (ap-∘ fst codes p₁) ∙ idp)) ◃∙
      ap (transport (_==_ base) p₂) (! q₃) ◃∙
      transp-cst=idf p₂ t ◃∎
    long-aux7 q₂ idp = pre-rotate'-out long-aux8 
