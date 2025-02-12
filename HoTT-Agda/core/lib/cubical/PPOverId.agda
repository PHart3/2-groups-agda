{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathOver
open import lib.cubical.PathPathOver

module lib.cubical.PPOverId where

module _ {i} {A : Type i} where

  PPOver-from-hnat-aux5 :
    {x : A} {e₁ e₃ : x == x} (q₁ : idp == e₃) (q₂ : idp == ! e₁)
    →
    ! (ap (λ p → p ∙ idp) (q₁ ∙ ! (∙-unit-r e₃)) ∙ ∙-assoc e₃ idp idp ∙ ∙-unit-r e₃) ∙
    ! (ap (λ p → p ∙ e₁) q₂ ∙ ap (λ q → q) (!-inv-l e₁) ∙ idp)
      ==
    ! (ap (λ p → p ∙ e₁)
        (ap2 _∙_ (q₁ ∙ ! (∙-unit-r e₃)) q₂ ∙
        (! (∙-assoc (e₃ ∙ idp) idp (! e₁)) ∙ ap (λ p → p ∙ ! e₁) (∙-assoc e₃ idp idp ∙ ∙-unit-r e₃)) ∙ idp) ∙
      ∙-assoc e₃ (! e₁) e₁ ∙ ap (_∙_ e₃) (!-inv-l e₁) ∙ ∙-unit-r e₃)
  PPOver-from-hnat-aux5 {e₁ = e₁} idp q₂ = ap (λ v → ! (ap (λ p → p ∙ e₁) v ∙ ap (λ q → q) (!-inv-l e₁) ∙ idp)) (lemma q₂)
    where
      lemma : {x : A} {e : x == x} (q : idp == e) →  q == ap2 _∙_ idp q ∙ idp
      lemma idp = idp

  PPOver-from-hnat-aux4 :
    {x y : A} {e₂ e₁ e₃ : x == y} (q₁ : idp == e₃ ∙ ! e₂) (q₂ : idp == e₂ ∙ ! e₁)
    →
    ! (ap (λ p → p ∙ e₂) q₁ ∙ ∙-assoc e₃ (! e₂) e₂ ∙ ap (_∙_ e₃) (!-inv-l e₂) ∙ ∙-unit-r e₃) ∙
    ! (ap (λ p → p ∙ e₁) q₂ ∙ ∙-assoc e₂ (! e₁) e₁ ∙ ap (_∙_ e₂) (!-inv-l e₁) ∙ ∙-unit-r e₂)
      ==
    ! (ap (λ p → p ∙ e₁)
        (ap2 _∙_ q₁ q₂ ∙
        (! (∙-assoc (e₃ ∙ ! e₂) e₂ (! e₁)) ∙
        ap (λ p → p ∙ ! e₁) (∙-assoc e₃ (! e₂) e₂ ∙ ap (_∙_ e₃) (!-inv-l e₂) ∙ ∙-unit-r e₃)) ∙ idp) ∙
      ∙-assoc e₃ (! e₁) e₁ ∙ ap (_∙_ e₃) (!-inv-l e₁) ∙ ∙-unit-r e₃)
  PPOver-from-hnat-aux4 {e₂ = idp} {e₁} {e₃} q₁ q₂ =
    (∙-unit-r-ind
      (λ {e} (q : idp == e ∙ idp)
        →
        (q' : idp == ! e₁)
        →
        ! (ap (λ p → p ∙ idp) q ∙ ∙-assoc e idp idp ∙ ∙-unit-r e) ∙
        ! (ap (λ p → p ∙ e₁) q' ∙ ap (λ q → q) (!-inv-l e₁) ∙ idp)
          ==
        ! (ap (λ p → p ∙ e₁)
            (ap2 _∙_ q q' ∙
            (! (∙-assoc (e ∙ idp) idp (! e₁)) ∙ ap (λ p → p ∙ ! e₁) (∙-assoc e idp idp ∙ ∙-unit-r e)) ∙ idp) ∙
          ∙-assoc e (! e₁) e₁ ∙ ap (_∙_ e) (!-inv-l e₁) ∙ ∙-unit-r e))
        PPOver-from-hnat-aux5)
      q₁ q₂

module _ {i j} {A : Type i} {B : Type j} (f g : A → B) where
    
  PPOver-from-hnat-aux3 :
    {x y : A} (r₂ : x == y) {e₁ : f y == g y} {e₂ : f x == g x} {e₃ : f x == g x}
    (q₁ : idp == e₃ ∙ ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙ ! e₁)
    → 
    ! (ap (λ p → p ∙ e₂) q₁ ∙ ∙-assoc e₃ (! e₂) e₂ ∙ ap (_∙_ e₃) (!-inv-l e₂) ∙ ∙-unit-r e₃) ∙ᵈ hmpty-nat-po== f g r₂ q₂
      ==
    hmpty-nat-po== f g r₂ (ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l-aux g r₂ e₃ e₂ e₁ ∙ idp)
  PPOver-from-hnat-aux3 idp q₁ q₂ = PPOver-from-hnat-aux4 q₁ q₂

  PPOver-from-hnat-aux2 :
    {x : A} (r₂ : x == x) {e₁ e₂ : f x == g x}
    (q₁ : idp == e₁ ∙ ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙ ! e₁)
    {q₃ : ap f r₂ == e₁ ∙ ap g r₂ ∙ ! e₁}
    →
    q₃ == ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e₁ e₂ idp r₂ ∙ idp
    →
    ! (ap (λ p → p ∙ e₂) q₁ ∙ ∙-assoc e₁ (! e₂) e₂ ∙ ap (_∙_ e₁) (!-inv-l e₂) ∙ ∙-unit-r e₁) ∙ᵈ hmpty-nat-po== f g r₂ q₂
      ==
    hmpty-nat-po== f g r₂ q₃
  PPOver-from-hnat-aux2 r₂ q₁ q₂ idp = PPOver-from-hnat-aux3 r₂ q₁ q₂

  PPOver-from-hnat-aux :
    {x y : A} (r₁ : x == y) (r₂ : y == x) {e₁ : f x == g x} {e₂ : f y == g y}
    (q₁ : ap f r₁ == e₁ ∙ ap g r₁ ∙ ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙ ! e₁)
    (q₃ : ap f (r₁ ∙ r₂) == e₁ ∙ ap g (r₁ ∙ r₂) ∙ ! e₁)
    →
    ∙-ap f r₁ r₂ ∙ q₃ == ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e₁ e₂ r₁ r₂ ∙ idp
    →
    hmpty-nat-po== f g r₁ {e₁ = e₁} q₁ ∙ᵈ hmpty-nat-po== f g r₂ q₂ == hmpty-nat-po== f g (r₁ ∙ r₂) q₃
  PPOver-from-hnat-aux idp r₂ q₁ q₂ q₃ τ = PPOver-from-hnat-aux2 r₂ q₁ q₂ τ

  PPOver-from-hnat :
    {x : A} (r₁ r₂ {r₃} : x == x) (s : r₁ ∙ r₂ == r₃) {e : f x == g x}
    (q₁ : ap f r₁ == e ∙ ap g r₁ ∙ ! e)
    (q₂ : ap f r₂ == e ∙ ap g r₂ ∙ ! e)
    (q₃ : ap f r₃ == e ∙ ap g r₃ ∙ ! e)
    →
    ∙-ap f r₁ r₂ ∙ ap (ap f) s ∙ q₃
      ==
    ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e e r₁ r₂ ∙ ap (λ p → e ∙ ap g p ∙ ! e) s
    → 
    PPOver s (hmpty-nat-po== f g r₁ {e₁ = e} q₁ ∙ᵈ hmpty-nat-po== f g r₂ q₂) (hmpty-nat-po== f g r₃ q₃) 
  PPOver-from-hnat r₁ r₂ idp q₁ q₂ q₃ τ = PPOver-from-hnat-aux r₁ r₂ q₁ q₂ q₃ τ 
