{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed

-- preservation of groupoid structure by ⊙-crd∼-to-==

module lib.types.PtdMap-conv where

module _ {i j} {X : Ptd i} {Y : Ptd j} where

  abstract

    !⊙-conv : {f₁ f₂ : X ⊙→ Y} (h : f₁ ⊙-crd∼ f₂) →
      ⊙-crd∼-to-== (!-⊙∼ h) == ! (⊙-crd∼-to-== h)
    !⊙-conv {f₁} = 
      ⊙hom-ind f₁
        (λ f₂ h → ⊙-crd∼-to-== (!-⊙∼ h) == ! (⊙-crd∼-to-== h))
        (ap ⊙-crd∼-to-== (∙⊙∼-! f₁) ∙
        ⊙-crd∼-to-==-β f₁ ∙
        ap ! (! (⊙-crd∼-to-==-β f₁)))

    ⊙∘-conv : {f₁ f₃ f₂ : X ⊙→ Y} (h₁ : f₁ ⊙-crd∼ f₂) (h₂ : f₂ ⊙-crd∼ f₃) →
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂) ◃∎ =ₛ ⊙-crd∼-to-== h₁ ◃∙ ⊙-crd∼-to-== h₂ ◃∎
    ⊙∘-conv {f₁} {f₃} =
      ⊙hom-ind f₁
        (λ f₂ h₁ →
          ((h₂ : f₂ ⊙-crd∼ f₃) →
            ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂) ◃∎ =ₛ ⊙-crd∼-to-== h₁ ◃∙ ⊙-crd∼-to-== h₂ ◃∎))
        λ h₂ → 
          ⊙-crd∼-to-== (⊙∼-id f₁ ∙⊙∼ h₂) ◃∎
            =ₛ₁⟨ ap ⊙-crd∼-to-== (∙⊙∼-unit-l h₂) ⟩
          ⊙-crd∼-to-== h₂ ◃∎
            =ₛ⟨ =ₛ-in (idp {a = ⊙-crd∼-to-== h₂}) ⟩
          idp {a = f₁} ◃∙ ⊙-crd∼-to-== h₂ ◃∎
            =ₛ₁⟨ 0 & 1 & ! (⊙-crd∼-to-==-β f₁) ⟩
          ⊙-crd∼-to-== (⊙∼-id f₁) ◃∙ ⊙-crd∼-to-== h₂ ◃∎ ∎ₛ
          
    ⊙∘-conv-tri : {f₁ f₂ f₃ f₄ : X ⊙→ Y}
      (h₁ : f₁ ⊙-crd∼ f₂) (h₂ : f₂ ⊙-crd∼ f₃) (h₃ : f₃ ⊙-crd∼ f₄) →
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃) ◃∎
        =ₛ
      ⊙-crd∼-to-== h₁ ◃∙ ⊙-crd∼-to-== h₂ ◃∙ ⊙-crd∼-to-== h₃ ◃∎
    ⊙∘-conv-tri h₁ h₂ h₃ =
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃) ◃∎
        =ₛ⟨ ⊙∘-conv h₁  (h₂ ∙⊙∼ h₃) ⟩
      ⊙-crd∼-to-== h₁ ◃∙ ⊙-crd∼-to-== (h₂ ∙⊙∼ h₃) ◃∎
        =ₛ⟨ 1 & 1 & ⊙∘-conv h₂ h₃ ⟩
      ⊙-crd∼-to-== h₁ ◃∙ ⊙-crd∼-to-== h₂ ◃∙ ⊙-crd∼-to-== h₃ ◃∎ ∎ₛ

    ⊙∘-conv-quint : {f₁ f₂ f₃ f₄ f₅ f₆ : X ⊙→ Y}
      (h₁ : _⊙-crd∼_ f₁ f₂) (h₂ : _⊙-crd∼_ f₂ f₃)
      (h₃ : _⊙-crd∼_ f₃ f₄) (h₄ : _⊙-crd∼_ f₄ f₅)
      (h₅ : _⊙-crd∼_ f₅ f₆) →
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== h₃ ◃∙
      ⊙-crd∼-to-== h₄ ◃∙
      ⊙-crd∼-to-== h₅ ◃∎ 
        =ₛ
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎
    ⊙∘-conv-quint h₁ h₂ h₃ h₄ h₅ = 
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== h₃ ◃∙
      ⊙-crd∼-to-== h₄ ◃∙
      ⊙-crd∼-to-== h₅ ◃∎
        =ₛ⟨ 2 & 3 & !ₛ (⊙∘-conv-tri h₃ h₄ h₅) ⟩
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri h₁ h₂ (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅)) ⟩
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎ ∎ₛ

    ⊙∘-conv-sept : {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : X ⊙→ Y}
      (h₁ : _⊙-crd∼_ f₁ f₂) (h₂ : _⊙-crd∼_ f₂ f₃)
      (h₃ : _⊙-crd∼_ f₃ f₄) (h₄ : _⊙-crd∼_ f₄ f₅)
      (h₅ : _⊙-crd∼_ f₅ f₆) (h₆ : _⊙-crd∼_ f₆ f₇)
      (h₇ : _⊙-crd∼_ f₇ f₈) →
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== h₃ ◃∙
      ⊙-crd∼-to-== h₄ ◃∙
      ⊙-crd∼-to-== h₅ ◃∙
      ⊙-crd∼-to-== h₆ ◃∙
      ⊙-crd∼-to-== h₇ ◃∎
        =ₛ
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎
    ⊙∘-conv-sept h₁ h₂ h₃ h₄ h₅ h₆ h₇ = 
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== h₃ ◃∙
      ⊙-crd∼-to-== h₄ ◃∙
      ⊙-crd∼-to-== h₅ ◃∙
      ⊙-crd∼-to-== h₆ ◃∙
      ⊙-crd∼-to-== h₇ ◃∎
        =ₛ⟨ 2 & 5 & ⊙∘-conv-quint h₃ h₄ h₅ h₆ h₇ ⟩
      ⊙-crd∼-to-== h₁ ◃∙
      ⊙-crd∼-to-== h₂ ◃∙
      ⊙-crd∼-to-== (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri h₁ h₂ (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇)) ⟩
      ⊙-crd∼-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎ ∎ₛ

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} where

  abstract

    whisk⊙-conv-r : {f₁ : X ⊙→ Y} {f₂ f₂' : Y ⊙→ Z} (h : f₂ ⊙-crd∼ f₂') →
      ⊙-crd∼-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-crd∼-to-== h)
    whisk⊙-conv-r {f₁} {f₂} =
      ⊙hom-ind f₂
        (λ f₂' h → ⊙-crd∼-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-crd∼-to-== h))
        (ap ⊙-crd∼-to-== (∙⊙-pre {f = f₂}) ∙
        ⊙-crd∼-to-==-β (f₂ ⊙∘ f₁) ∙
        ! (ap (ap (λ m → m ⊙∘ f₁)) (⊙-crd∼-to-==-β f₂)))

    whisk⊙-conv-l : {f₁ : Y ⊙→ Z} {f₂ f₂' : X ⊙→ Y} (h : f₂ ⊙-crd∼ f₂') →
      ⊙-crd∼-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-crd∼-to-== h)
    whisk⊙-conv-l {f₁} {f₂} = 
      ⊙hom-ind f₂
        (λ f₂' h → ⊙-crd∼-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-crd∼-to-== h))
        (ap ⊙-crd∼-to-== (∙⊙-post {f = f₂}) ∙ 
        ⊙-crd∼-to-==-β (f₁ ⊙∘ f₂) ∙
        ! (ap (ap (λ m → f₁ ⊙∘ m)) (⊙-crd∼-to-==-β f₂)))

    ⊙-whisk⊙-conv-l-∙-aux : {f₁ : Y ⊙→ Z} {f₂ f₂' : X ⊙→ Y} (h : f₂ ⊙-crd∼ f₂') →
      ap (_⊙∘_ f₁) (⊙-crd∼-to-== (⊙∼-id f₂) ∙ ⊙-crd∼-to-== h)
        ==
      ⊙-crd∼-to-== (⊙∘-post f₁ (⊙∼-id f₂ ∙⊙∼ h))
    ⊙-whisk⊙-conv-l-∙-aux {f₁@(_ , idp)} {f₂@(_ , idp)} =
      ⊙hom-ind f₂
        (λ f₂' h →
          ap (_⊙∘_ f₁) (⊙-crd∼-to-== (⊙∼-id f₂) ∙ ⊙-crd∼-to-== h)
            ==
          ⊙-crd∼-to-== (⊙∘-post f₁ (⊙∼-id f₂ ∙⊙∼ h)))
        (ap (λ p → ap (_⊙∘_ f₁) (p ∙ p)) (⊙-crd∼-to-==-β f₂) ∙
        ! (ap ⊙-crd∼-to-== (⊙→∼-to-== ((λ _ → idp) , idp )) ∙ ⊙-crd∼-to-==-β _))

    ⊙-whisk⊙-conv-l-∙ : {f₁ : Y ⊙→ Z} {f₂ f₂'' f₂' : X ⊙→ Y} (h₁ : f₂ ⊙-crd∼ f₂') (h₂ : f₂' ⊙-crd∼ f₂'') →
      ap (λ m → f₁ ⊙∘ m) (⊙-crd∼-to-== h₁ ∙ ⊙-crd∼-to-== h₂)
        ==
      ⊙-crd∼-to-== (⊙∘-post f₁ (h₁ ∙⊙∼ h₂))
    ⊙-whisk⊙-conv-l-∙ {f₁} {f₂} {f₂''} =
      ⊙hom-ind f₂
        (λ f₂' h₁ → (h₂ : f₂' ⊙-crd∼ f₂'') →
          ap (λ m → f₁ ⊙∘ m) (⊙-crd∼-to-== h₁ ∙ ⊙-crd∼-to-== h₂)
            ==
          ⊙-crd∼-to-== (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
        ⊙-whisk⊙-conv-l-∙-aux

    !⊙-whisk⊙-conv-l-∙ : {f₁ : Y ⊙→ Z} {f₂ f₂'' f₂' : X ⊙→ Y} (h₁ : f₂ ⊙-crd∼ f₂') (h₂ : f₂' ⊙-crd∼ f₂'') →
      ! (ap (λ m → f₁ ⊙∘ m) (⊙-crd∼-to-== h₁ ∙ ⊙-crd∼-to-== h₂))
        ==
      ⊙-crd∼-to-== (!-⊙∼ (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
    !⊙-whisk⊙-conv-l-∙ {f₁} h₁ h₂ = ap ! (⊙-whisk⊙-conv-l-∙ h₁ h₂) ∙ ! (!⊙-conv (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
