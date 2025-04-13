{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import lib.types.Unit
open import lib.types.Empty
open import lib.FTID

module lib.Univalence2 where

module _ {i} (A : Type i) where

  ap-ua-idf-idp : 
    ap ua (ap (idf A ,_)
      (prop-has-all-paths (snd (ide A)) (snd (ide A))))
      ==
    idp
  ap-ua-idf-idp =
    ap (ap ua) (ap (ap (idf A ,_)) (prop-has-all-paths {{has-level-apply-instance}} _ _))    
  
  ua-∘e-al-aux4 : (ω : ua (ide A) == ua (ide A) ∙ ua (ide A)) →
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ∙
    ap (_∙_ (ua (ide A))) (! ω) ∙
    ! ω ∙ ω ∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω))
      ==
    idp
  ua-∘e-al-aux4 =
    transport
      (λ p → ∀ (ω : p == p ∙ p) →
        ∙-assoc p p p ∙ ap (_∙_ p) (! ω) ∙ ! ω ∙ ω ∙
        ! (ap (λ v → v ∙ p) (! ω))
          ==
        idp) (! (ua-η idp)) (λ ω → =ₛ-out (aux ω))
    where
      aux : (ω : idp == idp)
        →
        ap (λ x → x) (! ω) ◃∙ ! ω ◃∙ ω ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ
        idp ◃∎
      aux ω = 
        ap (λ x → x) (! ω) ◃∙ ! ω ◃∙ ω ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 1 & 2 & !-inv-l ω ⟩
        ap (λ x → x) (! ω) ◃∙ idp ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-idf (! ω) ⟩
        ! ω ◃∙ idp ◃∙ ! (ap (λ v → v ∙ idp) (! ω)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap ! (ap-! (λ v → v ∙ idp) ω) ∙ !-! (ap (λ v → v ∙ idp) ω) ⟩
        ! ω ◃∙ idp ◃∙ ap (λ v → v ∙ idp) ω ◃∎
          =ₛ₁⟨ !-unit-r-inv ω ⟩
        idp ◃∎ ∎ₛ

  ua-∘e-al-aux3 : {e₁ e₂ : A ≃ A} (ω : e₁ == e₂) →
    ! (ap (λ z → ua (z ∘e ide A)) ω) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) ω) ◃∎
      =ₛ
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∎
  ua-∘e-al-aux3 {e₁} idp =
    =ₛ-in (∙-unit-r _ ∙ ap (ap ua) (ap (ap (–> e₁ ,_))
      (prop-has-all-paths {{has-level-apply-instance}} _ _)))
      
  ua-∘e-al-aux2 : (ω₁ : ua (ide A) == ua (ide A) ∙ ua (ide A))
    {e : A ≃ A} (ω₂ : e == ide A) →
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua ω₂ ∙ ω₁)) ◃∙
    ap (λ z → ua (ide A) ∙ ua z) ω₂ ◃∙
    ! (ap ua ω₂ ∙ ω₁) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    (ap ua ω₂ ∙ ω₁) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua ω₂)) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua ω₂ ∙ ω₁))) ◃∎
      =ₛ
    idp ◃∎
  ua-∘e-al-aux2 ω₁ idp = 
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (_∙_ (ua (ide A))) (! ω₁) ◃∙
    idp ◃∙
    ! ω₁ ◃∙
    ap ua (ap (fst (ide A) ,_)
      (prop-has-all-paths (snd (ide A)) (snd (ide A)))) ◃∙
    ω₁ ◃∙
    idp ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω₁)) ◃∎
      =ₛ₁⟨ 4 & 1 & ap-ua-idf-idp ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (_∙_ (ua (ide A))) (! ω₁) ◃∙
    idp ◃∙
    ! ω₁ ◃∙
    idp ◃∙
    ω₁ ◃∙
    idp ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! ω₁)) ◃∎
      =ₛ₁⟨ ua-∘e-al-aux4 ω₁ ⟩
    idp ◃∎ ∎ₛ
    
  ua-∘e-al-aux :
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
    ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A)))) ◃∎
      =ₛ
    idp ◃∎
  ua-∘e-al-aux =
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
    ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A)))) ◃∎
      =ₛ₁⟨ 1 & 1 & ap (ap (λ v → ua (ide A) ∙ v)) (ap ! (ua-∘e-β (ide A))) ⟩
    _
      =ₛ₁⟨ 2 & 1 & ap ! (ua-∘e-β (ide A ∘e ide A)) ⟩
    _
      =ₛ₁⟨ 5 & 1 & ap ! (ap (ap (λ v → v ∙ ua (ide A))) (ap ! (ua-∘e-β (ide A)))) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ua-∘e (ide A ∘e ide A) (ide A) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 4 & 1 & ua-∘e-coh (ide A) (∘e-unit-r (ide A)) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    ua-∘e (ide A) (ide A) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ₁⟨ 5 & 1 & ua-∘e-β (ide A) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ! (ap ua (∘e-unit-r (ide A ∘e ide A)) ∙
      ap (λ w → w ∙ ua (ide A ∘e ide A)) (! (ua-η idp))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 2 & 1 &
        hmtpy-nat-!◃ (λ z → ap ua (∘e-unit-r z) ∙ ap (λ w → w ∙ ua z) (! (ua-η idp))) (∘e-unit-r (ide A)) ⟩
    ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
    ap (λ v → ua (ide A) ∙ v)
      (! (ap ua (∘e-unit-r (ide A)) ∙
        ap (λ w → w ∙ ua (ide A)) (! (ua-η idp)))) ◃∙
    ap (λ z → ua (ide A) ∙ ua z) (∘e-unit-r (ide A)) ◃∙
    ! (ap ua (∘e-unit-r (ide A)) ∙ ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ z → ua (z ∘e ide A)) (∘e-unit-r (ide A))) ◃∙
    ap ua (pair= idp (prop-has-all-paths _ _)) ◃∙
    ap ua (ap (_∘e_ (ide A)) (∘e-unit-r (ide A))) ◃∙
    (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) ◃∙
    ! (ap (λ q → q ∙ ua (ide A)) (ap ua (∘e-unit-r (ide A)))) ◃∙
    ! (ap (λ v → v ∙ ua (ide A)) (! (ap ua (∘e-unit-r (ide A)) ∙
      ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))))) ◃∎
      =ₛ⟨ 4 & 3 & ua-∘e-al-aux3 (∘e-unit-r (ide A)) ⟩
    _
      =ₛ⟨ ua-∘e-al-aux2 (ap (λ w → w ∙ ua (ide A)) (! (ua-η idp))) (∘e-unit-r (ide A)) ⟩
    idp ◃∎ ∎ₛ

ua-∘e-al : ∀ {i} {A B C D : Type i} (e₁ : A ≃ B) (e₂ : B ≃ C) (e₃ : C ≃ D)
  →
  ∙-assoc (ua e₁) (ua e₂) (ua e₃) ◃∙
  ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
  ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
    =ₛ
  ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
  ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
  ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎
ua-∘e-al {i} =
  equiv-induction-tri
    (λ {A B C D} e₁ e₂ e₃ → 
      ∙-assoc (ua e₁) (ua e₂) (ua e₃) ◃∙
      ap (λ v → ua e₁ ∙ v) (! (ua-∘e e₂ e₃)) ◃∙
      ! (ua-∘e e₁ (e₃ ∘e e₂)) ◃∎
        =ₛ
      ap (λ v → v ∙ ua e₃) (! (ua-∘e e₁ e₂)) ◃∙
      ! (ua-∘e (e₂ ∘e e₁) e₃) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎)
    (λ A →
      ∙-assoc (ua (ide A)) (ua (ide A)) (ua (ide A)) ◃∙
      ap (λ v → ua (ide A) ∙ v) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A) (ide A ∘e ide A)) ◃∎
        =ₛ⟨ post-rotate-in (post-rotate-in (post-rotate'-out (ua-∘e-al-aux A))) ⟩
      idp ◃∙
      ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A ∘e ide A) (ide A)) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎
        =ₛ₁⟨ 0 & 2 & idp ⟩
      ap (λ v → v ∙ ua (ide A)) (! (ua-∘e (ide A) (ide A))) ◃∙
      ! (ua-∘e (ide A ∘e ide A) (ide A)) ◃∙
      ! (ap ua (pair= idp (prop-has-all-paths _ _))) ◃∎ ∎ₛ )
