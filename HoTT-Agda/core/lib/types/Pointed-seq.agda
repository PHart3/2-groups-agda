{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed

-- reasoning about equalities between sequences of pointed functions

module lib.types.Pointed-seq where

-- sequences to facilitate equational reasoning about pointed functions

infixr 80 _⊙-∙∙_
_⊙-∙∙_ : ∀ {i j k} {A : Ptd i} {B : Ptd j} {C : Ptd k}
  → A ⊙→-s B → B ⊙→-s C → A ⊙→-s C
_⊙-∙∙_ t [] = t
_⊙-∙∙_ t (s ⊙▹∙ p) = (t ⊙-∙∙ s) ⊙▹∙ p

⊙↯-∙∙ : ∀ {i j k} {A : Ptd i} {B : Ptd j} {C : Ptd k} (s : A ⊙→-s B) (t : B ⊙→-s C)
  → ⊙↯ (s ⊙-∙∙ t) == ⊙↯ t ⊙∘ ⊙↯ s
⊙↯-∙∙ s [] = ⊙-comp-to-== (⊙∘-lunit _)
⊙↯-∙∙ [] ([] ⊙▹∙ m) = idp
⊙↯-∙∙ (v ⊙▹∙ p) ([] ⊙▹∙ m) = idp
⊙↯-∙∙ s (v@(_ ⊙▹∙ _) ⊙▹∙ m) = ap (λ p → m ⊙∘ p) (⊙↯-∙∙ s v) ∙ ! (⊙λ= (⊙∘-assoc m _ (⊙↯ s)))

⊙point-from-start : ∀ {i j} {A : Ptd i} {B : Ptd j} (n : ℕ) (s : A ⊙→-s B) → Ptd i
⊙point-from-start {A = A} O s = A
⊙point-from-start {A = A} (S n) [] = A
⊙point-from-start (S n) (s ⊙▹∙ p) = ⊙point-from-start n s

⊙drop : ∀ {i j} {A : Ptd i} {B : Ptd j} (n : ℕ) (s : A ⊙→-s B) → ⊙point-from-start n s ⊙→-s B
⊙drop 0 s = s
⊙drop (S n) [] = []
⊙drop (S n) (s ⊙▹∙ p) = ⊙drop n s ⊙▹∙ p 

⊙take : ∀ {i j} {A : Ptd i} {B : Ptd j} (n : ℕ) (s : A ⊙→-s B) → A ⊙→-s ⊙point-from-start n s
⊙take O s = []
⊙take (S n) [] = []
⊙take (S n) (s ⊙▹∙ p) = ⊙take n s

private

  -- ad-hoc identity type for elements of Setω
  infix 30 _ω==_
  data _ω==_ {A : Agda.Primitive.Setω} (a : A) : A → Agda.Primitive.Setω where
    idp : a ω== a

  apω : {A B : Agda.Primitive.Setω} (f : A → B) {a b : A} (p : a ω== b) → f a ω== f b
  apω f idp = idp

  ap-⊙↯ : ∀ {i j} {A : Ptd i} {B : Ptd j} {f₁ f₂ : A ⊙→-s B} → f₁ ω== f₂ → ⊙↯ f₁ == ⊙↯ f₂
  ap-⊙↯ idp = idp

private
  ⊙take-drop-split' : ∀ {i j} {A : Ptd i} {B : Ptd j} (n : ℕ) (s : A ⊙→-s B)
    → s ω== ⊙take n s ⊙-∙∙ ⊙drop n s
  ⊙take-drop-split' O s = lemma s
    where
      lemma : ∀ {i j} {A : Ptd i} {B : Ptd j} (s : A ⊙→-s B) → s ω== [] ⊙-∙∙ s
      lemma [] = idp
      lemma (s ⊙▹∙ m) = apω (λ s → s ⊙▹∙ m) (lemma s)
  ⊙take-drop-split' (S n) [] = idp
  ⊙take-drop-split' (S n) (s ⊙▹∙ p) = apω (λ v → v ⊙▹∙ p) (⊙take-drop-split' n s)

⊙take-drop-split : ∀ {i j} {A : Ptd i} {B : Ptd j} (n : ℕ) (s : A ⊙→-s B)
  → ⊙↯ s == ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ (⊙take n s)
⊙take-drop-split n s =
  ⊙↯ s
    =⟨ ap-⊙↯ (⊙take-drop-split' n s) ⟩
  ⊙↯ (⊙take n s ⊙-∙∙ ⊙drop n s)
    =⟨ ⊙↯-∙∙ (⊙take n s) (⊙drop n s) ⟩
  ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ (⊙take n s) =∎

infix 30 _=⊙↯=_
_=⊙↯=_ : ∀ {i j} {A : Ptd i} {B : Ptd j} → A ⊙→-s B → A ⊙→-s B → Type (lmax i j)
_=⊙↯=_ s t = (⊙↯ s) == (⊙↯ t)

module _ {i j} {A : Ptd i} {B : Ptd j} where

  infixr 80 _⊙∙ₛ_
  _⊙∙ₛ_ : {s t u : A ⊙→-s B} → s ⊙=ₛ t → t ⊙=ₛ u → s ⊙=ₛ u
  _⊙∙ₛ_ (⊙=ₛ-in p) (⊙=ₛ-in q) = ⊙=ₛ-in (p ∙ q)

  abstract
    private
      infixr 10 _=⊙↯=⟨_&_&_&_⟩_
      _=⊙↯=⟨_&_&_&_⟩_ : {q : A ⊙→ B}
        → (s : A ⊙→-s B)
        → (n : ℕ) (m : ℕ)
        → (t : ⊙point-from-start m (⊙take n s) ⊙→-s ⊙point-from-start n s)
        → ⊙drop m (⊙take n s) =⊙↯= t
        → ⊙↯ ((⊙take m (⊙take n s) ⊙-∙∙ t) ⊙-∙∙ ⊙drop n s) == q
        → ⊙↯ s == q
      _=⊙↯=⟨_&_&_&_⟩_ {q} s n m t p p' =
        ⊙↯ s
          =⟨ ⊙take-drop-split n s ⟩
        ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ (⊙take n s)
          =⟨ ap (⊙↯ (⊙drop n s) ⊙∘_) (⊙take-drop-split m (⊙take n s)) ⟩
        ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ (⊙drop m (⊙take n s)) ⊙∘ ⊙↯ (⊙take m (⊙take n s))
          =⟨ ap (λ v → ⊙↯ (⊙drop n s) ⊙∘ v ⊙∘ ⊙↯ (⊙take m (⊙take n s))) p ⟩
        ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ t ⊙∘ ⊙↯ (⊙take m (⊙take n s))
          =⟨ ap (λ v → ⊙↯ (⊙drop n s) ⊙∘ v) (! (⊙↯-∙∙ (⊙take m (⊙take n s)) t)) ⟩
        ⊙↯ (⊙drop n s) ⊙∘ ⊙↯ (⊙take m (⊙take n s) ⊙-∙∙ t)
          =⟨ ! (⊙↯-∙∙ (⊙take m (⊙take n s) ⊙-∙∙ t) (⊙drop n s)) ⟩
        ⊙↯ ((⊙take m (⊙take n s) ⊙-∙∙ t) ⊙-∙∙ ⊙drop n s)
          =⟨ p' ⟩
        q =∎

    infixr 10 _⊙=ₛ⟨_&_&_⟩_
    _⊙=ₛ⟨_&_&_⟩_ : (s : A ⊙→-s B) {u : A ⊙→-s B}
      → (n m : ℕ)
      → {r : ⊙point-from-start m (⊙take n s) ⊙→-s ⊙point-from-start n s}
      → ⊙drop m (⊙take n s) ⊙=ₛ r
      → ((⊙take m (⊙take n s) ⊙-∙∙ r) ⊙-∙∙ ⊙drop n s) ⊙=ₛ u
      → s ⊙=ₛ u
    _⊙=ₛ⟨_&_&_⟩_ s m n {r} p p' = ⊙=ₛ-in (s =⊙↯=⟨ m & n & r & ⊙=ₛ-out p ⟩ ⊙=ₛ-out p')

    infixr 10 _⊙=ₛ⟨_⟩_
    _⊙=ₛ⟨_⟩_ : (s : A ⊙→-s B) {t u : A ⊙→-s B}
      → s ⊙=ₛ t
      → t ⊙=ₛ u
      → s ⊙=ₛ u
    _⊙=ₛ⟨_⟩_ _ p q = p ⊙∙ₛ q
