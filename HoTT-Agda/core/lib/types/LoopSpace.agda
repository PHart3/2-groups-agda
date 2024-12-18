{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Sigma

module lib.types.LoopSpace where

{- loop space -}

module _ {i} where

  ⊙Ω : Ptd i → Ptd i
  ⊙Ω ⊙[ A , a ] = ⊙[ (a == a) , idp ]

  Ω : Ptd i → Type i
  Ω = de⊙ ∘ ⊙Ω

module _ {i} {X : Ptd i} where

  Ω-! : Ω X → Ω X
  Ω-! = !

  Ω-∙ : Ω X → Ω X → Ω X
  Ω-∙ = _∙_

{- pointed versions of functions on paths -}

⊙Ω-∙ : ∀ {i} {X : Ptd i} → ⊙Ω X ⊙× ⊙Ω X ⊙→ ⊙Ω X
⊙Ω-∙ = (uncurry Ω-∙ , idp)

⊙Ω-fmap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Ω X ⊙→ ⊙Ω Y
⊙Ω-fmap (f , idp) = ap f , idp

Ω-fmap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → (Ω X → Ω Y)
Ω-fmap F = fst (⊙Ω-fmap F)

Ω-fmap-β : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) (p : Ω X)
  → Ω-fmap F p == ! (snd F) ∙ ap (fst F) p ∙' snd F
Ω-fmap-β (_ , idp) _ = idp

Ω-fmap-β∙ : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) (p : Ω X)
  → Ω-fmap F p == ! (snd F) ∙ ap (fst F) p ∙ snd F
Ω-fmap-β∙ (f , idp) p = ! (∙-unit-r (ap f p))

Ω-fmap-pt-β : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y)
  → snd (⊙Ω-fmap F) ==
    Ω-fmap-β F idp ∙ ap (λ p → ! (snd F) ∙ p) (∙'-unit-l (snd F)) ∙ !-inv-l (snd F) 
Ω-fmap-pt-β (_ , idp) = idp

Ω-isemap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  (F : X ⊙→ Y) → is-equiv (fst F) → is-equiv (Ω-fmap F)
Ω-isemap (f , idp) e = ap-is-equiv e _ _

Ω-emap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → (X ⊙≃ Y) → (Ω X ≃ Ω Y)
Ω-emap (F , F-is-equiv) = Ω-fmap F , Ω-isemap F F-is-equiv

⊙Ω-emap : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → (X ⊙≃ Y) → (⊙Ω X ⊙≃ ⊙Ω Y)
⊙Ω-emap (F , F-is-equiv) = ⊙Ω-fmap F , Ω-isemap F F-is-equiv

⊙Ω-fmap2 : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → X ⊙× Y ⊙→ Z → ⊙Ω X ⊙× ⊙Ω Y ⊙→ ⊙Ω Z
⊙Ω-fmap2 (f , idp) = (λ{(p , q) → ap2 (curry f) p q}) , idp

⊙Ω-fmap-∘ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Ω-fmap (g ⊙∘ f) == ⊙Ω-fmap g ⊙∘ ⊙Ω-fmap f
⊙Ω-fmap-∘ (g , idp) (f , idp) = ⊙λ=' (λ p → ap-∘ g f p) idp

⊙Ω-csmap : ∀ {i₀ i₁ j₀ j₁} {X₀ : Ptd i₀} {X₁ : Ptd i₁}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁} {f : X₀ ⊙→ Y₀} {g : X₁ ⊙→ Y₁}
  {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquare f g hX hY
  → ⊙CommSquare (⊙Ω-fmap f) (⊙Ω-fmap g) (⊙Ω-fmap hX) (⊙Ω-fmap hY)
⊙Ω-csmap {f = f} {g} {hX} {hY} (⊙comm-sqr cs) = ⊙comm-sqr $ ⊙app= $
  ⊙Ω-fmap hY ⊙∘ ⊙Ω-fmap f
    =⟨ ! $ ⊙Ω-fmap-∘ hY f ⟩
  ⊙Ω-fmap (hY ⊙∘ f)
    =⟨ ap ⊙Ω-fmap $ ⊙λ= cs ⟩
  ⊙Ω-fmap (g ⊙∘ hX)
    =⟨ ⊙Ω-fmap-∘ g hX ⟩
  ⊙Ω-fmap g ⊙∘ ⊙Ω-fmap hX
    =∎

⊙Ω-csemap : ∀ {i₀ i₁ j₀ j₁} {X₀ : Ptd i₀} {X₁ : Ptd i₁}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁} {f : X₀ ⊙→ Y₀} {g : X₁ ⊙→ Y₁}
  {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquareEquiv f g hX hY
  → ⊙CommSquareEquiv (⊙Ω-fmap f) (⊙Ω-fmap g) (⊙Ω-fmap hX) (⊙Ω-fmap hY)
⊙Ω-csemap {f = f} {g} {hX} {hY} (⊙comm-sqr cs , hX-ise , hY-ise) =
  (⊙comm-sqr $ ⊙app= $
    ⊙Ω-fmap hY ⊙∘ ⊙Ω-fmap f
      =⟨ ! $ ⊙Ω-fmap-∘ hY f ⟩
    ⊙Ω-fmap (hY ⊙∘ f)
      =⟨ ap ⊙Ω-fmap $ ⊙λ= cs ⟩
    ⊙Ω-fmap (g ⊙∘ hX)
      =⟨ ⊙Ω-fmap-∘ g hX ⟩
    ⊙Ω-fmap g ⊙∘ ⊙Ω-fmap hX
      =∎) ,
  Ω-isemap hX hX-ise , Ω-isemap hY hY-ise

⊙Ω-fmap-idf : ∀ {i} {X : Ptd i} → ⊙Ω-fmap (⊙idf X) == ⊙idf _
⊙Ω-fmap-idf = ⊙λ=' ap-idf idp

⊙Ω-sect : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
  → has-sect⊙ f → has-sect⊙ (⊙Ω-fmap f)
has-sect⊙.r-inv (⊙Ω-sect f (sect⊙ r-inv sect⊙-eq)) = ⊙Ω-fmap r-inv
has-sect⊙.sect⊙-eq (⊙Ω-sect f (sect⊙ r-inv sect⊙-eq)) =
  ! (! (ap (⊙Ω-fmap) sect⊙-eq ∙ ⊙Ω-fmap-idf) ∙ ⊙Ω-fmap-∘ f r-inv)

⊙Ω-fmap2-fst : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Ω-fmap2 {X = X} {Y = Y} ⊙fst == ⊙fst
⊙Ω-fmap2-fst = ⊙λ=' (uncurry ap2-fst) idp

⊙Ω-fmap2-snd : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  → ⊙Ω-fmap2 {X = X} {Y = Y} ⊙snd == ⊙snd
⊙Ω-fmap2-snd = ⊙λ=' (uncurry ap2-snd) idp

⊙Ω-fmap-fmap2 : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (G : Z ⊙→ W) (F : X ⊙× Y ⊙→ Z)
  → ⊙Ω-fmap G ⊙∘ ⊙Ω-fmap2 F == ⊙Ω-fmap2 (G ⊙∘ F)
⊙Ω-fmap-fmap2 (g , idp) (f , idp) =
  ⊙λ=' (uncurry (ap-ap2 g (curry f))) idp

⊙Ω-fmap2-fmap : ∀ {i j k l m}
  {X : Ptd i} {Y : Ptd j} {U : Ptd k} {V : Ptd l} {Z : Ptd m}
  (G : (U ⊙× V) ⊙→ Z) (F₁ : X ⊙→ U) (F₂ : Y ⊙→ V)
  → ⊙Ω-fmap2 G ⊙∘ ⊙×-fmap (⊙Ω-fmap F₁) (⊙Ω-fmap F₂) == ⊙Ω-fmap2 (G ⊙∘ ⊙×-fmap F₁ F₂)
⊙Ω-fmap2-fmap (g , idp) (f₁ , idp) (f₂ , idp) =
  ⊙λ=' (λ {(p , q) → ap2-ap-l (curry g) f₁ p (ap f₂ q)
                   ∙ ap2-ap-r (λ x v → g (f₁ x , v)) f₂ p q})
       idp

⊙Ω-fmap2-diag : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙× X ⊙→ Y)
  → ⊙Ω-fmap2 F ⊙∘ ⊙diag == ⊙Ω-fmap (F ⊙∘ ⊙diag)
⊙Ω-fmap2-diag (f , idp) = ⊙λ=' (ap2-diag (curry f)) idp

Ω-fmap-∙ : ∀ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) (p q : Ω X)
  → Ω-fmap F (p ∙ q) == Ω-fmap F p ∙ Ω-fmap F q
Ω-fmap-∙ (f , idp) p q = ap-∙ f p q
