{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics

-- ad-hoc data strucutre for a big path-seq reduction

module KLoop-ptr-comp-red where

module _ {i} {A : Type i} where

  module _
    {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ x₁₇ x₁₈ x₁₉ x₂₀ x₂₁ x₂₂ x₂₃ x₂₄ x₂₅ x₂₆ x₂₇ x₂₈ x₂₉ : A}
    {p₁ : x₁ == x₂} {p₂ : x₂ == x₃} {p₃ : x₃ == x₄} {p₄ : x₄ == x₅} {p₅ : x₅ == x₆} {p₆ : x₆ == x₇} {p₇ : x₇ == x₈} {p₈ : x₈ == x₉}
    {p₉ : x₉ == x₁₀} {p₁₀ : x₁₀ == x₁₁} {p₁₁ : x₁₁ == x₁₂} {p₁₂ : x₁₂ == x₁₃} {p₁₃ : x₁₃ == x₁₄} {p₁₄ : x₁₄ == x₁₅} {p₁₅ : x₁₅ == x₁₆}
    {p₁₆ : x₁₆ == x₁₇} {p₁₇ : x₁₇ == x₁₈} {p₁₈ : x₁₈ == x₁₉} {p₁₉ : x₁₉ == x₂₀} {p₂₀ : x₂₀ == x₂₁} {p₂₁ : x₂₁ == x₂₂} {p₂₂ : x₂₂ == x₂₃}
    {p₂₃ : x₂₃ == x₂₄} {p₂₄ : x₂₄ == x₂₅} {p₂₅ : x₂₅ == x₂₆} {p₂₆ : x₂₆ == x₂₇} {p₂₇ : x₂₇ == x₂₈} {p₂₈ : x₂₈ == x₂₉}
    {q₁ : _} {q₂ : _} {q₃ : _} {q₄ : _} {q₅ : _} {q₆ : _} {q₇ : _} {r : _}
    (red-step1 : p₁₀ ∙ p₁₁ ∙ p₁₂ ∙ p₁₃ ∙ p₁₄ == q₁)
    (red-step2 : p₉ ∙ q₁ ∙ p₁₅ ∙ p₁₆ == q₂)
    (red-step3 : p₂₀ ∙ p₂₁ ∙ p₂₂ ∙ p₂₃ ∙ p₂₄ == q₃)
    (red-step4 : p₁₈ ∙ p₁₉ ∙ q₃ ∙ p₂₅ == q₄)
    (red-step5 : p₄ ∙ p₅ ∙ p₆ ∙ p₇ ∙ p₈ == q₅)
    (red-step6 : p₃ ∙ q₅ ∙ q₂ ∙ p₁₇ == q₆)
    (red-step7 : p₂ ∙ q₆ ∙ q₄ ∙ p₂₆ ∙ p₂₇ == q₇)
    (red-step8 : p₁ ∙ q₇ ∙ p₂₈ == r)
    where

    abstract
      Reduce◃28 : 
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ p₉ ◃∙ p₁₀ ◃∙ p₁₁ ◃∙ idp ◃∙ p₁₂ ◃∙ p₁₃ ◃∙
        p₁₄ ◃∙ p₁₅ ◃∙ p₁₆ ◃∙ p₁₇ ◃∙ p₁₈ ◃∙ p₁₉ ◃∙ p₂₀ ◃∙ p₂₁ ◃∙ idp ◃∙ p₂₂ ◃∙ idp ◃∙ idp ◃∙ p₂₃ ◃∙ p₂₄ ◃∙
        p₂₅ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ
        r ◃∎
      Reduce◃28 =
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ p₉ ◃∙ p₁₀ ◃∙ p₁₁ ◃∙ idp ◃∙ p₁₂ ◃∙ p₁₃ ◃∙
        p₁₄ ◃∙ p₁₅ ◃∙ p₁₆ ◃∙ p₁₇ ◃∙ p₁₈ ◃∙ p₁₉ ◃∙ p₂₀ ◃∙ p₂₁ ◃∙ idp ◃∙ p₂₂ ◃∙ idp ◃∙ idp ◃∙ p₂₃ ◃∙ p₂₄ ◃∙
        p₂₅ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 10 & 6 & red-step1 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ p₉ ◃∙ q₁ ◃∙ p₁₅ ◃∙ p₁₆ ◃∙ p₁₇ ◃∙
        p₁₈ ◃∙ p₁₉ ◃∙ p₂₀ ◃∙ p₂₁ ◃∙ idp ◃∙ p₂₂ ◃∙ idp ◃∙ idp ◃∙ p₂₃ ◃∙ p₂₄ ◃∙ p₂₅ ◃∙ idp ◃∙ p₂₆ ◃∙
        p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 9 & 4 & red-step2 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ q₂ ◃∙ p₁₇ ◃∙ p₁₈ ◃∙ p₁₉ ◃∙ p₂₀ ◃∙
        p₂₁ ◃∙ idp ◃∙ p₂₂ ◃∙ idp ◃∙ idp ◃∙ p₂₃ ◃∙ p₂₄ ◃∙ p₂₅ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙
        idp ◃∙ idp ◃∎
          =ₛ₁⟨ 13 & 8 & red-step3 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ q₂ ◃∙ p₁₇ ◃∙ p₁₈ ◃∙ p₁₉ ◃∙ q₃ ◃∙
        p₂₅ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 11 & 4 & red-step4 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ p₄ ◃∙ p₅ ◃∙ p₆ ◃∙ p₇ ◃∙ p₈ ◃∙ q₂ ◃∙ p₁₇ ◃∙ q₄ ◃∙ idp ◃∙ p₂₆ ◃∙
        p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 4 & 5 & red-step5 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ p₃ ◃∙ q₅ ◃∙ q₂ ◃∙ p₁₇ ◃∙ q₄ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 3 & 4 & red-step6 ⟩
        idp ◃∙ p₁ ◃∙ p₂ ◃∙ q₆ ◃∙ q₄ ◃∙ idp ◃∙ p₂₆ ◃∙ p₂₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ 2 & 6 & red-step7 ⟩
        idp ◃∙ p₁ ◃∙ q₇ ◃∙ p₂₈ ◃∙ idp ◃∙ idp ◃∙ idp ◃∎
          =ₛ₁⟨ ap (λ q → p₁ ∙ q₇ ∙ q) (∙-unit-r p₂₈) ∙ red-step8 ⟩
        r ◃∎ ∎ₛ
