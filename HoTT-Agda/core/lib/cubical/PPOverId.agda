{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.PathOver
open import lib.cubical.PathPathOver

module lib.cubical.PPOverId where

module _ {i} {A : Type i} where

  PPOver-from-hnat-aux5 :
    {x : A} {e₁ p : x == x} (r : idp == p) (q' : idp == idp ∙' ! e₁)
    →
    ∙-idp-!-∙'-rot p idp (r ∙ ! (∙-unit-r p)) ∙ ap ! (q' ∙ ∙'-unit-l (! e₁)) ∙ !-! e₁
      ==
    ∙-idp-!-∙'-rot p e₁ (ap2 _∙_ (r ∙ ! (∙-unit-r p)) q' ∙ ∙-assoc2-!-inv-l-aux2 p idp e₁ ∙ idp)
  PPOver-from-hnat-aux5 {x} {e₁} idp q' = lemma q'
    where
      lemma : {v : x == x} (q : v == idp ∙' ! e₁)  →
        ap ! (q ∙ ∙'-unit-l (! e₁)) ∙ !-! e₁
          ==
        ap ! ((ap2 _∙_ idp q ∙ ∙-assoc2-!-inv-l-aux2 idp idp e₁ ∙ idp) ∙ ∙'-unit-l (! e₁)) ∙ !-! e₁
      lemma idp = lemma2 e₁
        where
          lemma2 : {y : A} (e : y == x) →
            ap ! (∙'-unit-l (! e)) ∙ !-! e
              ==
            ap ! ((∙-assoc2-!-inv-l-aux2 idp idp e ∙ idp) ∙ ∙'-unit-l (! e)) ∙ !-! e
          lemma2 idp = idp

  PPOver-from-hnat-aux4 :
    {x y : A} {e₂ e₁ e₃ : x == y} (q₁ : idp == e₃ ∙ idp ∙' ! e₂) (q₂ : idp == e₂ ∙ idp ∙' ! e₁)
    →
    ∙-idp-!-∙'-rot e₃ e₂ q₁ ∙ ∙-idp-!-∙'-rot e₂ e₁ q₂
      ==
    ∙-idp-!-∙'-rot e₃ e₁ (ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l-aux2 e₃ e₂ e₁ ∙ idp)
  PPOver-from-hnat-aux4 {e₂ = idp} {e₁} {e₃} q₁ q₂ =
    (∙-unit-r-ind
      (λ {e} (q : idp == e ∙ idp)
        →
        (q' : idp == idp ∙' ! e₁)
        →
        ∙-idp-!-∙'-rot e idp q ∙ ap ! (q' ∙ ∙'-unit-l (! e₁)) ∙ !-! e₁
          ==
        ∙-idp-!-∙'-rot e e₁ (ap2 _∙_ q q' ∙ ∙-assoc2-!-inv-l-aux2 e idp e₁ ∙ idp))
        PPOver-from-hnat-aux5)
      q₁ q₂

module _ {i j} {A : Type i} {B : Type j} (f g : A → B) where

  PPOver-from-hnat-aux3 :
    {x y : A} (r₂ : x == y) {e₁ : f y == g y} {e₂ : f x == g x} {e₃ : f x == g x}
    (q₁ : idp == e₃ ∙ idp ∙' ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙' ! e₁)
    → 
    ∙-idp-!-∙'-rot e₃ e₂ q₁ ∙ᵈ from-hmtpy-nat f g r₂ q₂
      ==
    from-hmtpy-nat f g r₂ (ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l-aux g r₂ e₃ e₂ e₁ ∙ idp)
  PPOver-from-hnat-aux3 idp q₁ q₂ = PPOver-from-hnat-aux4 q₁ q₂

  PPOver-from-hnat-aux2 :
    {x : A} (r₂ : x == x) {e₁ e₂ : f x == g x}
    (q₁ : idp == e₁ ∙ idp ∙' ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙' ! e₁)
    {q₃ : ap f r₂ == e₁ ∙ ap g r₂ ∙' ! e₁}
    →
    q₃ == ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e₁ e₂ idp r₂ ∙ idp
    →
    ∙-idp-!-∙'-rot e₁ e₂ q₁ ∙ᵈ from-hmtpy-nat f g r₂ q₂
      ==
    from-hmtpy-nat f g r₂ q₃
  PPOver-from-hnat-aux2 r₂ q₁ q₂ idp = PPOver-from-hnat-aux3 r₂ q₁ q₂

  PPOver-from-hnat-aux :
    {x y : A} (r₁ : x == y) (r₂ : y == x) {e₁ : f x == g x} {e₂ : f y == g y}
    (q₁ : ap f r₁ == e₁ ∙ ap g r₁ ∙' ! e₂)
    (q₂ : ap f r₂ == e₂ ∙ ap g r₂ ∙' ! e₁)
    (q₃ : ap f (r₁ ∙ r₂) == e₁ ∙ ap g (r₁ ∙ r₂) ∙' ! e₁)
    →
    ∙-ap f r₁ r₂ ∙ q₃ == ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e₁ e₂ r₁ r₂ ∙ idp
    →
    from-hmtpy-nat f g r₁ {e₁ = e₁} q₁ ∙ᵈ from-hmtpy-nat f g r₂ q₂ == from-hmtpy-nat f g (r₁ ∙ r₂) q₃
  PPOver-from-hnat-aux idp r₂ q₁ q₂ q₃ τ = PPOver-from-hnat-aux2 r₂ q₁ q₂ τ

  PPOver-from-hnat :
    {x : A} (r₁ r₂ {r₃} : x == x) (s : r₁ ∙ r₂ == r₃) {e : f x == g x}
    (q₁ : ap f r₁ == e ∙ ap g r₁ ∙' ! e)
    (q₂ : ap f r₂ == e ∙ ap g r₂ ∙' ! e)
    (q₃ : ap f r₃ == e ∙ ap g r₃ ∙' ! e)
    →
    ∙-ap f r₁ r₂ ∙ ap (ap f) s ∙ q₃
      ==
    ap2 _∙_ q₁ q₂ ∙ ∙-assoc2-!-inv-l g e e r₁ r₂ ∙ ap (λ p → e ∙ ap g p ∙' ! e) s
    → 
    PPOver s (from-hmtpy-nat f g r₁ {e₁ = e} q₁ ∙ᵈ from-hmtpy-nat f g r₂ q₂) (from-hmtpy-nat f g r₃ q₃) 
  PPOver-from-hnat r₁ r₂ idp q₁ q₂ q₃ τ = PPOver-from-hnat-aux r₁ r₂ q₁ q₂ q₃ τ 
