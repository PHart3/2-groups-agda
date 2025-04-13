{-# OPTIONS --without-K --rewriting #-}

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

    ⊙∘-conv-quint : {f₁ f₂ f₃ f₄ f₅ f₆ : X ⊙→ Y}
      (h₁ : _⊙-comp_ f₁ f₂) (h₂ : _⊙-comp_ f₂ f₃)
      (h₃ : _⊙-comp_ f₃ f₄) (h₄ : _⊙-comp_ f₄ f₅)
      (h₅ : _⊙-comp_ f₅ f₆) →
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== h₃ ◃∙
      ⊙-comp-to-== h₄ ◃∙
      ⊙-comp-to-== h₅ ◃∎ 
        =ₛ
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎
    ⊙∘-conv-quint h₁ h₂ h₃ h₄ h₅ = 
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== h₃ ◃∙
      ⊙-comp-to-== h₄ ◃∙
      ⊙-comp-to-== h₅ ◃∎
        =ₛ⟨ 2 & 3 & !ₛ (⊙∘-conv-tri h₃ h₄ h₅) ⟩
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri h₁ h₂ (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅)) ⟩
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅) ◃∎ ∎ₛ

    ⊙∘-conv-sept : {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : X ⊙→ Y}
      (h₁ : _⊙-comp_ f₁ f₂) (h₂ : _⊙-comp_ f₂ f₃)
      (h₃ : _⊙-comp_ f₃ f₄) (h₄ : _⊙-comp_ f₄ f₅)
      (h₅ : _⊙-comp_ f₅ f₆) (h₆ : _⊙-comp_ f₆ f₇)
      (h₇ : _⊙-comp_ f₇ f₈) →
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== h₃ ◃∙
      ⊙-comp-to-== h₄ ◃∙
      ⊙-comp-to-== h₅ ◃∙
      ⊙-comp-to-== h₆ ◃∙
      ⊙-comp-to-== h₇ ◃∎
        =ₛ
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎
    ⊙∘-conv-sept h₁ h₂ h₃ h₄ h₅ h₆ h₇ = 
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== h₃ ◃∙
      ⊙-comp-to-== h₄ ◃∙
      ⊙-comp-to-== h₅ ◃∙
      ⊙-comp-to-== h₆ ◃∙
      ⊙-comp-to-== h₇ ◃∎
        =ₛ⟨ 2 & 5 & ⊙∘-conv-quint h₃ h₄ h₅ h₆ h₇ ⟩
      ⊙-comp-to-== h₁ ◃∙
      ⊙-comp-to-== h₂ ◃∙
      ⊙-comp-to-== (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎
        =ₛ⟨ !ₛ (⊙∘-conv-tri h₁ h₂ (h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇)) ⟩
      ⊙-comp-to-== (h₁ ∙⊙∼ h₂ ∙⊙∼ h₃ ∙⊙∼ h₄ ∙⊙∼ h₅ ∙⊙∼ h₆ ∙⊙∼ h₇) ◃∎ ∎ₛ

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} where

  abstract

    whisk⊙-conv-r : {f₁ : X ⊙→ Y} {f₂ f₂' : Y ⊙→ Z} (h : f₂ ⊙-comp f₂') →
      ⊙-comp-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-comp-to-== h)
    whisk⊙-conv-r {f₁} {f₂} =
      ⊙hom-ind f₂
        (λ f₂' h → ⊙-comp-to-== (⊙∘-pre f₁ h) == ap (λ m → m ⊙∘ f₁) (⊙-comp-to-== h))
        (ap ⊙-comp-to-== (∙⊙-pre {f = f₂}) ∙
        ⊙-comp-to-==-β (f₂ ⊙∘ f₁) ∙
        ! (ap (ap (λ m → m ⊙∘ f₁)) (⊙-comp-to-==-β f₂)))

    whisk⊙-conv-l : {f₁ : Y ⊙→ Z} {f₂ f₂' : X ⊙→ Y} (h : f₂ ⊙-comp f₂') →
      ⊙-comp-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h)
    whisk⊙-conv-l {f₁} {f₂} = 
      ⊙hom-ind f₂
        (λ f₂' h → ⊙-comp-to-== (⊙∘-post f₁ h) == ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h))
        (ap ⊙-comp-to-== (∙⊙-post {f = f₂}) ∙ 
        ⊙-comp-to-==-β (f₁ ⊙∘ f₂) ∙
        ! (ap (ap (λ m → f₁ ⊙∘ m)) (⊙-comp-to-==-β f₂)))

    ⊙-whisk⊙-conv-l-∙-aux : {f₁ : Y ⊙→ Z} {f₂ f₂' : X ⊙→ Y} (h : f₂ ⊙-comp f₂') →
      ap (_⊙∘_ f₁) (⊙-comp-to-== (⊙∼-id f₂) ∙ ⊙-comp-to-== h)
        ==
      ⊙-comp-to-== (⊙∘-post f₁ (⊙∼-id f₂ ∙⊙∼ h))
    ⊙-whisk⊙-conv-l-∙-aux {f₁@(_ , idp)} {f₂@(_ , idp)} =
      ⊙hom-ind f₂
        (λ f₂' h →
          ap (_⊙∘_ f₁) (⊙-comp-to-== (⊙∼-id f₂) ∙ ⊙-comp-to-== h)
            ==
          ⊙-comp-to-== (⊙∘-post f₁ (⊙∼-id f₂ ∙⊙∼ h)))
        (ap (λ p → ap (_⊙∘_ f₁) (p ∙ p)) (⊙-comp-to-==-β f₂) ∙
        ! (ap ⊙-comp-to-== (⊙→∼-to-== ((λ _ → idp) , idp )) ∙ ⊙-comp-to-==-β _))

    ⊙-whisk⊙-conv-l-∙ : {f₁ : Y ⊙→ Z} {f₂ f₂'' f₂' : X ⊙→ Y} (h₁ : f₂ ⊙-comp f₂') (h₂ : f₂' ⊙-comp f₂'') →
      ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h₁ ∙ ⊙-comp-to-== h₂)
        ==
      ⊙-comp-to-== (⊙∘-post f₁ (h₁ ∙⊙∼ h₂))
    ⊙-whisk⊙-conv-l-∙ {f₁} {f₂} {f₂''} =
      ⊙hom-ind f₂
        (λ f₂' h₁ → (h₂ : f₂' ⊙-comp f₂'') →
          ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h₁ ∙ ⊙-comp-to-== h₂)
            ==
          ⊙-comp-to-== (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
        ⊙-whisk⊙-conv-l-∙-aux

    !⊙-whisk⊙-conv-l-∙ : {f₁ : Y ⊙→ Z} {f₂ f₂'' f₂' : X ⊙→ Y} (h₁ : f₂ ⊙-comp f₂') (h₂ : f₂' ⊙-comp f₂'') →
      ! (ap (λ m → f₁ ⊙∘ m) (⊙-comp-to-== h₁ ∙ ⊙-comp-to-== h₂))
        ==
      ⊙-comp-to-== (!-⊙∼ (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
    !⊙-whisk⊙-conv-l-∙ {f₁} h₁ h₂ = ap ! (⊙-whisk⊙-conv-l-∙ h₁ h₂) ∙ ! (!⊙-conv (⊙∘-post f₁ (h₁ ∙⊙∼ h₂)))
