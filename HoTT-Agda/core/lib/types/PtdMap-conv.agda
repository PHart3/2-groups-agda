{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.types.Pointed

-- preservation of groupoid structure by ⊙-comp-to-==

module lib.types.PtdMap-conv where

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  abstract

    !⊙-conv : {f₁ f₂ : X ⊙→ Y} (h : f₁ ⊙-comp f₂) →
      ⊙-comp-to-== (!-⊙∼ h) == ! (⊙-comp-to-== h)
    !⊙-conv {f₁} = 
      ⊙hom-ind f₁
        (λ f₂ h → ⊙-comp-to-== (!-⊙∼ h) == ! (⊙-comp-to-== h))
        (ap ⊙-comp-to-== (∙⊙∼-! f₁) ∙
        ⊙-comp-to-==-β f₁ ∙
        ap ! (! (⊙-comp-to-==-β f₁)))

    ⊙∘-conv : {f₁ f₃ f₂ : X ⊙→ Y} (h₁ : f₁ ⊙-comp f₂) (h₂ : f₂ ⊙-comp f₃) →
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂) ◃∎ =ₛ ⊙-comp-to-== h₁ ◃∙ ⊙-comp-to-== h₂ ◃∎
    ⊙∘-conv {f₁} {f₃} =
      ⊙hom-ind f₁
        (λ f₂ h₁ →
          ((h₂ : f₂ ⊙-comp f₃) →
            ⊙-comp-to-== (h₁ ∙⊙∼ h₂) ◃∎ =ₛ ⊙-comp-to-== h₁ ◃∙ ⊙-comp-to-== h₂ ◃∎))
        λ h₂ → 
          ⊙-comp-to-== (⊙∼-id f₁ ∙⊙∼ h₂) ◃∎
            =ₛ₁⟨ ap ⊙-comp-to-== (∙⊙∼-unit-l h₂) ⟩
          ⊙-comp-to-== h₂ ◃∎
            =ₛ⟨ =ₛ-in (idp {a = ⊙-comp-to-== h₂}) ⟩
          idp {a = f₁} ◃∙ ⊙-comp-to-== h₂ ◃∎
            =ₛ₁⟨ 0 & 1 & ! (⊙-comp-to-==-β f₁) ⟩
          ⊙-comp-to-== (⊙∼-id f₁) ◃∙ ⊙-comp-to-== h₂ ◃∎ ∎ₛ
          
    ⊙∘-conv-tri : {f₁ f₂ f₃ f₄ : X ⊙→ Y}
      (h₁ : f₁ ⊙-comp f₂) (h₂ : f₂ ⊙-comp f₃) (h₃ : f₃ ⊙-comp f₄) →
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃) ◃∎
        =ₛ
      ⊙-comp-to-== h₁ ◃∙ ⊙-comp-to-== h₂ ◃∙ ⊙-comp-to-== h₃ ◃∎
    ⊙∘-conv-tri h₁ h₂ h₃ =
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃) ◃∎
        =ₛ⟨ ⊙∘-conv h₁  (h₂ ∙⊙∼ h₃) ⟩
      ⊙-comp-to-== h₁ ◃∙ ⊙-comp-to-== (h₂ ∙⊙∼ h₃) ◃∎
        =ₛ⟨ 1 & 1 & ⊙∘-conv h₂ h₃ ⟩
      ⊙-comp-to-== h₁ ◃∙ ⊙-comp-to-== h₂ ◃∙ ⊙-comp-to-== h₃ ◃∎ ∎ₛ
      
  module _ {k} {Z : Ptd k} where

    abstract
    
      whisk⊙-conv-r : {f₁ : X ⊙→ Y} {f₂ f₂' : Y ⊙→ Z} (h : f₂ ⊙-comp f₂') →
        ⊙-comp-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-comp-to-== h)
      whisk⊙-conv-r {f₁} {f₂} =
        ⊙hom-ind f₂
          (λ f₂' h → ⊙-comp-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-comp-to-== h))
          (ap ⊙-comp-to-== ∙⊙-pre ∙
          ⊙-comp-to-==-β (f₂ ⊙∘ f₁) ∙
          ! (ap (ap (λ m → m ⊙∘ f₁)) (⊙-comp-to-==-β f₂)))

      whisk⊙-conv-l : {f₁ : Y ⊙→ Z} {f₂ f₂' : X ⊙→ Y} (h : f₂ ⊙-comp f₂') →
        ⊙-comp-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h)
      whisk⊙-conv-l {f₁} {f₂} = 
        ⊙hom-ind f₂
          (λ f₂' h → ⊙-comp-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h))
          (ap ⊙-comp-to-== ∙⊙-post ∙ 
          ⊙-comp-to-==-β (f₁ ⊙∘ f₂) ∙
          ! (ap (ap (λ m → f₁ ⊙∘ m)) (⊙-comp-to-==-β f₂)))
