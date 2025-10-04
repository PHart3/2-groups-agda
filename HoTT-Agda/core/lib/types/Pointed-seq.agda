{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed

-- sequences to facilitate equational reasoning about pointed functions

module lib.types.Pointed-seq where

module _ {i : ULevel} where

  infixr 80 _⊙◃∙_
  data ⊙→-Seq : Ptd i → Ptd i → Type (lsucc i) where
    [] : {A : Ptd i} → ⊙→-Seq A A
    _⊙◃∙_ : {A B C : Ptd i} (m : B ⊙→ C) (s : ⊙→-Seq A B) → ⊙→-Seq A C

  infix 30 _⊙→-s_
  _⊙→-s_ = ⊙→-Seq

  infix 90 _⊙◃∎
  _⊙◃∎ : {A A' : Ptd i} → A ⊙→ A' → A ⊙→-s A'
  _⊙◃∎ m = m ⊙◃∙ []

  ⊙↯ : {A A' : Ptd i} (s : A ⊙→-s A') → A ⊙→ A'
  ⊙↯ [] = ⊙idf _
  ⊙↯ (m ⊙◃∙ []) = m
  ⊙↯ {A = A} {A'} (m ⊙◃∙ s@(_ ⊙◃∙ _)) = m ⊙∘ ⊙↯ s

  record _⊙=ₛ_ {A A' : Ptd i} (s t : A ⊙→-s A') : Type i where
    constructor ⊙=ₛ-in
    field
      ⊙=ₛ-out : ⊙↯ s == ⊙↯ t
  open _⊙=ₛ_ public
  
  infix 15 _⊙∎ₛ
  _⊙∎ₛ : {A A' : Ptd i} (s : A ⊙→-s A') → s ⊙=ₛ s
  _⊙∎ₛ _ = ⊙=ₛ-in idp 

  infixr 80 _⊙-∙∙_
  _⊙-∙∙_ :  {A B C : Ptd i} → A ⊙→-s B → B ⊙→-s C → A ⊙→-s C
  _⊙-∙∙_ t [] = t
  _⊙-∙∙_ t (p ⊙◃∙ s) = p ⊙◃∙ (t ⊙-∙∙ s)

  ⊙↯-∙∙ : {A B C : Ptd i} (s : A ⊙→-s B) (t : B ⊙→-s C)
    → ⊙↯ (s ⊙-∙∙ t) == ⊙↯ t ⊙∘ ⊙↯ s
  ⊙↯-∙∙ s [] = ⊙-comp-to-== (⊙∘-lunit _)
  ⊙↯-∙∙ [] (m ⊙◃∙ []) = idp
  ⊙↯-∙∙ (p ⊙◃∙ v) (m ⊙◃∙ []) = idp
  ⊙↯-∙∙ s (m ⊙◃∙ v@(_ ⊙◃∙ _)) = ap (λ p → m ⊙∘ p) (⊙↯-∙∙ s v) ∙ ! (⊙λ= (⊙∘-assoc m _ (⊙↯ s)))

  ⊙point-from-end : {A B : Ptd i} (n : ℕ) (s : A ⊙→-s B) → Ptd i
  ⊙point-from-end {B = B} O s = B
  ⊙point-from-end {B = B} (S n) [] = B
  ⊙point-from-end (S n) (p ⊙◃∙ s) = ⊙point-from-end n s

  ⊙take : {A B : Ptd i} (n : ℕ) (s : A ⊙→-s B) → ⊙point-from-end n s ⊙→-s B
  ⊙take 0 s = []
  ⊙take (S n) [] = []
  ⊙take (S n) (p ⊙◃∙ s) = p ⊙◃∙ ⊙take n s 

  ⊙drop : {A B : Ptd i} (n : ℕ) (s : A ⊙→-s B) → A ⊙→-s ⊙point-from-end n s
  ⊙drop O s = s
  ⊙drop (S n) [] = []
  ⊙drop (S n) (p ⊙◃∙ s) = ⊙drop n s

  private
    ⊙drop-take-split' : {A B : Ptd i} (n : ℕ) (s : A ⊙→-s B)
      → s == ⊙drop n s ⊙-∙∙ ⊙take n s
    ⊙drop-take-split' O s = idp
    ⊙drop-take-split' (S n) [] = idp
    ⊙drop-take-split' (S n) (p ⊙◃∙ s) = ap (λ v → p ⊙◃∙ v) (⊙drop-take-split' n s)

  ⊙drop-take-split : {A B : Ptd i} (n : ℕ) (s : A ⊙→-s B)
    → ⊙↯ s == ⊙↯ (⊙take n s) ⊙∘ ⊙↯ (⊙drop n s)
  ⊙drop-take-split n s =
    ⊙↯ s
      =⟨ ap ⊙↯ (⊙drop-take-split' n s) ⟩
    ⊙↯ (⊙drop n s ⊙-∙∙ ⊙take n s)
      =⟨ ⊙↯-∙∙ (⊙drop n s) (⊙take n s) ⟩
    ⊙↯ (⊙take n s) ⊙∘ ⊙↯ (⊙drop n s) =∎

  infix 30 _=⊙↯=_
  _=⊙↯=_ : {A B : Ptd i} → A ⊙→-s B → A ⊙→-s B → Type i
  _=⊙↯=_ s t = (⊙↯ s) == (⊙↯ t)

  module _ {A B : Ptd i} where

    infixr 80 _⊙∙ₛ_
    _⊙∙ₛ_ : {s t u : A ⊙→-s B} → s ⊙=ₛ t → t ⊙=ₛ u → s ⊙=ₛ u
    _⊙∙ₛ_ (⊙=ₛ-in p) (⊙=ₛ-in q) = ⊙=ₛ-in (p ∙ q)

    abstract
      private
        infixr 10 _=⊙↯=⟨_&_&_&_⟩_
        _=⊙↯=⟨_&_&_&_⟩_ : {q : A ⊙→ B}
          → (s : A ⊙→-s B)
          → (n : ℕ) (m : ℕ)
          → (t : ⊙point-from-end m (⊙drop n s) ⊙→-s ⊙point-from-end n s)
          → ⊙take m (⊙drop n s) =⊙↯= t
          → ⊙↯ ((⊙drop m (⊙drop n s) ⊙-∙∙ t) ⊙-∙∙ ⊙take n s) == q
          → ⊙↯ s == q
        _=⊙↯=⟨_&_&_&_⟩_ {q} s n m t p p' =
          ⊙↯ s
            =⟨ ⊙drop-take-split n s ⟩
          ⊙↯ (⊙take n s) ⊙∘ ⊙↯ (⊙drop n s)
            =⟨ ap (⊙↯ (⊙take n s) ⊙∘_) (⊙drop-take-split m (⊙drop n s)) ⟩
          ⊙↯ (⊙take n s) ⊙∘ ⊙↯ (⊙take m (⊙drop n s)) ⊙∘ ⊙↯ (⊙drop m (⊙drop n s))
            =⟨ ap (λ v → ⊙↯ (⊙take n s) ⊙∘ v ⊙∘ ⊙↯ (⊙drop m (⊙drop n s))) p ⟩
          ⊙↯ (⊙take n s) ⊙∘ ⊙↯ t ⊙∘ ⊙↯ (⊙drop m (⊙drop n s))
            =⟨ ap (λ v → ⊙↯ (⊙take n s) ⊙∘ v) (! (⊙↯-∙∙ (⊙drop m (⊙drop n s)) t)) ⟩
          ⊙↯ (⊙take n s) ⊙∘ ⊙↯ (⊙drop m (⊙drop n s) ⊙-∙∙ t)
            =⟨ ! (⊙↯-∙∙ (⊙drop m (⊙drop n s) ⊙-∙∙ t) (⊙take n s)) ⟩
          ⊙↯ ((⊙drop m (⊙drop n s) ⊙-∙∙ t) ⊙-∙∙ ⊙take n s)
            =⟨ p' ⟩
          q =∎

      infixr 10 _⊙=ₛ⟨_&_&_⟩_
      _⊙=ₛ⟨_&_&_⟩_ : (s : A ⊙→-s B) {u : A ⊙→-s B}
        → (n m : ℕ)
        → {r : ⊙point-from-end m (⊙drop n s) ⊙→-s ⊙point-from-end n s}
        → ⊙take m (⊙drop n s) ⊙=ₛ r
        → ((⊙drop m (⊙drop n s) ⊙-∙∙ r) ⊙-∙∙ ⊙take n s) ⊙=ₛ u
        → s ⊙=ₛ u
      _⊙=ₛ⟨_&_&_⟩_ s m n {r} p p' = ⊙=ₛ-in (s =⊙↯=⟨ m & n & r & ⊙=ₛ-out p ⟩ ⊙=ₛ-out p')

      infixr 10 _⊙=ₑ⟨_&_&_%_⟩_
      _⊙=ₑ⟨_&_&_%_⟩_ : (s : A ⊙→-s B) {u : A ⊙→-s B}
        → (n m : ℕ)
        → (r : ⊙point-from-end m (⊙drop n s) ⊙→-s ⊙point-from-end n s)
        → ⊙take m (⊙drop n s) ⊙=ₛ r
        → ((⊙drop m (⊙drop n s) ⊙-∙∙ r) ⊙-∙∙ ⊙take n s) ⊙=ₛ u
        → s ⊙=ₛ u
      _⊙=ₑ⟨_&_&_%_⟩_ s m n r p p' = ⊙=ₛ-in (s =⊙↯=⟨ m & n & r & ⊙=ₛ-out p ⟩ ⊙=ₛ-out p')

      infixr 10 _⊙=ₛ⟨_⟩_
      _⊙=ₛ⟨_⟩_ : (s : A ⊙→-s B) {t u : A ⊙→-s B}
        → s ⊙=ₛ t
        → t ⊙=ₛ u
        → s ⊙=ₛ u
      _⊙=ₛ⟨_⟩_ _ p q = p ⊙∙ₛ q

      infixr 10 _⊙=ₛ₁⟨_⟩_
      _⊙=ₛ₁⟨_⟩_ : (s : A ⊙→-s B) {u : A ⊙→-s B}
        → {r : A ⊙→ B}
        → ⊙↯ s == r
        → r ⊙◃∎ ⊙=ₛ u
        → s ⊙=ₛ u
      _⊙=ₛ₁⟨_⟩_ s {r} p p' = ⊙=ₛ-in p ⊙∙ₛ p'

      infixr 10 _⊙=ₛ₁⟨_&_&_⟩_
      _⊙=ₛ₁⟨_&_&_⟩_ : (s : A ⊙→-s B) {u : A ⊙→-s B}
        → (n m : ℕ)
        → {r : ⊙point-from-end m (⊙drop n s) ⊙→ ⊙point-from-end n s}
        → ⊙↯ (⊙take m (⊙drop n s)) == r
        → (r ⊙◃∙ ⊙drop m (⊙drop n s)) ⊙-∙∙ ⊙take n s ⊙=ₛ u
        → s ⊙=ₛ u
      _⊙=ₛ₁⟨_&_&_⟩_ s m n {r} p p' = s ⊙=ₛ⟨ m & n & ⊙=ₛ-in {t = r ⊙◃∎} p ⟩ p'
