{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.PathGroupoid where

module _ {i} {A : Type i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one, but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 80 _∙'_

  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  ∙=∙' : {x y z : A} (p : x == y) (q : y == z)
    → p ∙ q == p ∙' q
  ∙=∙' idp idp = idp

  ∙'=∙ : {x y z : A} (p : x == y) (q : y == z)
    → p ∙' q == p ∙ q
  ∙'=∙ idp idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp _ _ = idp

  ∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙' q) ∙' r == p ∙' (q ∙' r)
  ∙'-assoc _ _ idp = idp

  ∙∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙∙'-assoc idp _ _ = idp

  ∙∙'-assoc' : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙∙'-assoc' _ _ idp = idp

  ∙'∙-∙∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙' q) ∙ r == p ∙ (q ∙ r)
  ∙'∙-∙∙-assoc p idp r = idp

  assoc-4-∙ : {x₁ x₂ x₃ x₄ x₅ x₆ : A} (p₁ : x₁ == x₂) (p₂ : x₂ == x₃) (p₃ : x₃ == x₄) (p₄ : x₄ == x₅) (p₅ : x₅ == x₆)
    → p₁ ∙ p₂ ∙ p₃ ∙ p₄ ∙ p₅ == (p₁ ∙ p₂ ∙ p₃) ∙ p₄ ∙ p₅
  assoc-4-∙ idp idp p₃ p₄ p₅ = idp 

  -- [∙-unit-l] and [∙'-unit-r] are definitional

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  ∙'-unit-l : {x y : A} (q : x == y) → idp ∙' q == q
  ∙'-unit-l idp = idp

  ∙ʳ-unit-l : {x y : A} (p : x == y) → idp ∙ʳ p == p
  ∙ʳ-unit-l idp = idp

  {- Reversal of paths -}

  ! : {x y : A} → (x == y → y == x)
  ! idp = idp

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp

  !-inv'-l : {x y : A} (p : x == y) → (! p) ∙' p == idp
  !-inv'-l idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

  !-inv'-r : {x y : A} (p : x == y) → p ∙' (! p) == idp
  !-inv'-r idp = idp

  {- Interactions between operations

  A lemma of the form [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  and so on.
  -}

  !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  !-∙ idp idp = idp

  !-∙◃ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) ◃∎ =ₛ ! q ◃∙ ! p ◃∎
  !-∙◃ idp idp = =ₛ-in idp

  !-∙ʳ : {x y z : A} (p₁ : y == z) (p₂ : x == y) → ! (p₁ ∙ʳ p₂) == ! p₂ ∙ʳ ! p₁
  !-∙ʳ idp idp = idp

  !-∙-∙ : {x y z w : A} (p : x == y) (q : y == z) (r : z == w)
    → ! (p ∙ q ∙ r) == ! r ∙ ! q ∙ ! p
  !-∙-∙ idp idp idp = idp

  ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  ∙-! idp idp = idp

  !-∙' : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙' q) == ! q ∙' ! p
  !-∙' idp idp = idp

  ∙'-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙' ! p == ! (p ∙' q)
  ∙'-! idp idp = idp

  !-! : {x y : A} (p : x == y) → ! (! p) == p
  !-! idp = idp

  !-!-∙ : {x y z : A} (p₁ : x == y) (p₂ : x == z)
    → ! (! p₁ ∙ p₂) ◃∎ =ₛ ! p₂ ◃∙ p₁ ◃∎
  !-!-∙ idp idp = =ₛ-in idp

  !-∙-! : {x y z : A} (p₁ : x == y) (p₂ : z == y)
    → ! (p₁ ∙ ! p₂) ◃∎ =ₛ p₂ ◃∙ ! p₁ ◃∎
  !-∙-! idp idp = =ₛ-in idp

  ∙-idp-!-∙'-rot : {x y : A} (p q : x == y) → idp == p ∙ idp ∙' ! q → p == q
  ∙-idp-!-∙'-rot idp q e = ap ! (e ∙ ∙'-unit-l (! q)) ∙ !-! q

  !-inv-r-front : {x y z : A} (p₁ : x == y) (p₂ : z == y) → p₁ ∙ʳ ! p₁ ∙ʳ p₂ == p₂
  !-inv-r-front idp idp = idp

{- induction rules for !-! -}
module _ {i j} {A : Type i} {x y : A} {p : x == y} where

  !-!-r-ind : {B : {q : y == x} → (p == ! q) → Type j}
    → ({q : x == y} (r : p == q) → B (r ∙ ! (!-! q))) → ((q : y == x) (r : p == ! q) → B r)
  !-!-r-ind {B} e idp idp = e idp

  !-!-l-ind : {B : {q : y == x} → (! q == p) → Type j}
    → ({q : x == y} (r : p == q) → B (!-! q ∙ ! r)) → ((q : y == x) (r : ! q == p) → B r)
  !-!-l-ind {B} e idp idp = e idp

{- induction rule for ∙-unit-r -}
module _ {i j} {A : Type i} {x y : A} {q : x == y} (B : {p : x == y} → (q == p ∙ idp) → Type j) where

  ∙-unit-r-ind : ({p : x == y} (r : q == p) → B (r ∙ ! (∙-unit-r p))) → ({p : x == y} (r : q == p ∙ idp) → B r)
  ∙-unit-r-ind e {p = idp} idp = e idp

{- combined induction rule -}
module _ {i j} {A : Type i} {x y : A} {q : y == x} (B : {p : x == y} → (! p ∙ idp == q) → Type j) where

  !-!-∙-unit-r-ind : ({p : y == x} (r : p == q) → B (∙-unit-r (! (! p)) ∙ !-! p ∙ r))
    → ({p : x == y} (r : ! p ∙ idp == q) → B r)
  !-!-∙-unit-r-ind e {p = idp} idp = e idp

{- additional algebraic lemmas -}

module _ {i} {A : Type i} where

  !-idp : {x : A} (p : x == x) → ! p == idp → p == idp
  !-idp p e = ! (!-! p) ∙ ap ! e

  !-unit-r-inv : {x : A} {v : x == x} (p : idp == v)
    → ! p ∙ ap (λ v → v ∙ idp) p == ! (∙-unit-r v)
  !-unit-r-inv idp = idp

  ∙-assoc-!-! : {x₁ x₂ x₃ x₄ x₅ x₆ : A} (p₁ : x₁ == x₂) (p₂ : x₂ == x₃) (p₃ : x₃ == x₄)
    (q₁ : x₆ == x₅) (q₂ : x₅ == x₄)
    → (p₁ ∙ p₂ ∙ p₃) ∙ ! (q₁ ∙ q₂) == p₁ ∙ p₂ ∙ p₃ ∙ ! q₂ ∙ ! q₁
  ∙-assoc-!-! idp idp idp idp idp = idp

  ∙-assoc2-!-inv-r : {x y z w : A} (p₁ : x == y) (p₂ : y == z) (p₃ : z == w)
    → p₁ ∙ p₂ == (p₁ ∙ p₂ ∙ p₃) ∙ ! p₃
  ∙-assoc2-!-inv-r idp idp idp = idp

  ∙-assoc2-∙2 : {x y z w u v : A} (p₁ : x == y) (p₂ : y == z)
    (p₃ : z == w) (p₄ : w == u) (p₅ : u == v)
    → p₁ ∙ (p₂ ∙ p₃) ∙ p₄ ∙ p₅ == (p₁ ∙ p₂) ∙ p₃ ∙ p₄ ∙ p₅
  ∙-assoc2-∙2 idp idp _ _ _ = idp 

  ∙-assoc-pentagon : {v w x y z : A} (p : v == w) (q : w == x) (r : x == y) (s : y == z)
    → ∙-assoc (p ∙ q) r s ◃∙
      ∙-assoc p q (r ∙ s) ◃∎
      =ₛ
      ap (λ u → u ∙ s) (∙-assoc p q r) ◃∙
      ∙-assoc p (q ∙ r) s ◃∙
      ap (λ u → p ∙ u) (∙-assoc q r s) ◃∎
  ∙-assoc-pentagon idp idp r s = =ₛ-in idp

  idp-canc-l-! : {x y : A} {p : x == x} (q : x == y) → p == idp → ! p ∙ q == q
  idp-canc-l-! idp e = ap (λ c → ! c ∙ idp) e

  canc-l-!-idp : {x y : A} {p : x == x} (q : x == y) → ! p ∙ q == q → p == idp
  canc-l-!-idp {p = p} idp e = !-idp p (! (∙-unit-r (! p)) ∙ e) 

  tri-id : {x y z : A} (p : x == y) (q : y == z)
    → ap (λ v → v ∙ q) (∙-unit-r p) == ! (! (∙-assoc p idp q)) ∙ idp
  tri-id idp q = idp

  pent-id : {x y z w u : A} (p₁ : x == y) (p₂ : y == z)
    (p₃ : z == w) (p₄ : w == u)
    →
    ! (∙-assoc p₁ p₂ (p₃ ∙ p₄)) ∙ ! (∙-assoc (p₁ ∙ p₂) p₃ p₄)
    ==
    ap (λ v → p₁ ∙ v) (! (∙-assoc p₂ p₃ p₄)) ∙
    ! (∙-assoc p₁ (p₂ ∙ p₃) p₄) ∙
    ap (λ v → v ∙ p₄) (! (∙-assoc p₁ p₂ p₃))
  pent-id idp idp _ _ = idp

  zz-id1 : {x y : A} (p : x == y)
    →
    idp
    ==
    ap (λ v → v ∙ p) (! (!-inv-r p)) ∙
    ! (! (∙-assoc p (! p) p)) ∙
    ap (λ v → p ∙ v) (!-inv-l p) ∙
    ∙-unit-r p
  zz-id1 idp = idp

  zz-id2 : {x y : A} (p : x == y)
    →
    idp
    ==
    ! (∙-unit-r (! p)) ∙
    ap (λ v → ! p ∙ v) (! (!-inv-r p)) ∙
    ! (∙-assoc (! p) p (! p)) ∙
    ap (λ v → v ∙ ! p) (!-inv-l p)
  zz-id2 idp = idp

  ∙-∙'-!-rot : {x y z w : A} (p₀ : x == y) (p₁ : x == z) (p₂ : z == w) (p₃ : y == w)
    → p₀ == p₁ ∙ p₂  ∙' ! p₃ → p₂ == ! p₁ ∙ p₀ ∙' p₃
  ∙-∙'-!-rot p₀ idp p₂ idp e = ! e

  !-inj-rot : {x y : A} {p₁ p₂ : x == y} (n : p₁ == p₂) {m : ! p₁ == ! p₂}
    → m == ap ! n →  ! (!-! p₁) ∙ ap ! m ∙' !-! p₂ == n
  !-inj-rot {p₁ = idp} idp idp = idp

  !-!∙!∙ : {x y z w : A} (p₁ : x == y) (p₂ : z == x) (p₃ : z == w)
    → ! (! p₁ ∙ ! p₂ ∙ p₃) ◃∎ =ₛ ! p₃ ◃∙ p₂ ◃∙ p₁ ◃∎
  !-!∙!∙ idp idp idp = =ₛ-in idp

  ∙'-!-∙-∙ : {x y z w : A} (p₁ : x == y) (p₂ : z == y) (p₃ : y == w)
    → (p₁ ∙' ! p₂) ∙ p₂ ∙ p₃ == p₁ ∙ p₃
  ∙'-!-∙-∙ p₁ idp p₃ = idp

  !-inv-l-r-unit-assoc : {x y : A} (p : x == y) →
    ! (ap (λ c → p ∙ c) (!-inv-l p) ∙ ∙-unit-r p) ∙
    ! (∙-assoc p (! p) p) ∙ ap (λ c → c ∙ p) (!-inv-r p)
    == idp
  !-inv-l-r-unit-assoc idp = idp

  assoc-tri-!-mid : {x y z w u v : A} (p₀ : x == y) (p₁ : y == z) (p₂ : w == z)
    (p₃ : z == u) (p₄ : u == v)
    → (p₀ ∙ p₁ ∙' ! p₂) ∙ p₂ ∙ p₃ ∙' p₄ == p₀ ∙ (p₁ ∙ p₃) ∙' p₄
  assoc-tri-!-mid idp p₁ p₂ p₃ idp = ∙'-!-∙-∙ p₁ p₂ p₃

  assoc-tri-!-coher : {x y : A} (p : x == y) →
    ! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))
      ==
    ap (λ q → q ∙ idp)
      (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))) ∙
    ap (_∙_ (p ∙ idp ∙' ! p))
      (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))) ∙
    assoc-tri-!-mid p idp p idp (! p) ∙ idp
  assoc-tri-!-coher idp = idp

  inv-rid : {x y : A} (p : x == y) → ! p ∙ p ∙ idp == idp
  inv-rid idp = idp

  !3-∙3 : {x y z w : A} (p : x == y) (q : z == y) (r : w == y)
    → ! ((p ∙ ! q) ∙ q ∙ ! r) ∙ p == r
  !3-∙3 idp idp r = ∙-unit-r (! (! r)) ∙ !-! r

  ∙-∙'-= : {x y : A} {p r : x == y} (q : x == x)
    → p == r → ! p ∙ q ∙' p == ! r ∙ q ∙' r
  ∙-∙'-= q idp = idp

  rot-in-flip : {x y z : A} (q : y == x) (r : y == z) {p : _} → p == ! q ∙ r → r ◃∎ =ₛ q ◃∙ p ◃∎
  rot-in-flip idp idp idp = =ₛ-in idp

  bi-rot : {x y z w : A} {p : y == x} {q : y == z} {s : z == w} {r : x == w}
    → r == ! p ∙ q ∙ s → s == ! q ∙ p ∙ r
  bi-rot {p = idp} {q = idp} {s = idp} idp = idp

  tri-exch : {x y z : A} {p : y == x} {q : y == z} {r : x == z}
    → ! p ∙ q == r → p == q ∙ ! r
  tri-exch {p = idp} {q = idp} {r} e = ap ! e

  tri-exch◃ : {x y z : A} {p₁ : x == y} {p₂ : z == y} {p₃ : z == x}
    → p₁ ◃∙ ! p₂ ◃∙ p₃ ◃∎ =ₛ idp ◃∎ → ! p₂ ◃∎ =ₛ ! p₁ ◃∙ ! p₃ ◃∎
  tri-exch◃ {p₁ = idp} {p₂ = idp} e = =ₛ-in (ap ! (! (=ₛ-out e)))

  tri-rot : {a₁ a₂ a₃ a₄ a₅ : A} (q₁ : a₁ == a₂) (q₂ : a₃ == a₂)
    (q₃ : a₃ == a₄) (q₄ : a₄ == a₅) {p : a₁ == a₅}
    → p == q₁ ∙ ! q₂ ∙ q₃ ∙ q₄
    → q₁ == p ∙ ! q₄ ∙ ! q₃ ∙ q₂
  tri-rot idp idp idp idp idp = idp 

  tri-rot2 : {a₁ a₂ a₃ a₄ a₅ : A} (q₁ : a₁ == a₂) (q₂ : a₃ == a₂)
    (q₃ : a₃ == a₄) (q₄ : a₄ == a₅) {p : a₁ == a₅}
    → p == q₁ ∙ ! q₂ ∙ q₃ ∙ q₄
    → q₃ == q₂ ∙ ! q₁ ∙ p ∙ ! q₄
  tri-rot2 idp idp idp idp idp = idp 

  !-!-tri-rot : {a₁ a₂ a₃ a₄ a₅ : A}
    (p₁ : a₁ == a₂) (p₄ : a₃ == a₁) (p₃ : a₃ == a₄)
    (p₂ : a₄ == a₅) {p₅ : a₅ == a₂}
    → p₁ ◃∎ =ₛ ! (! p₂ ∙ ! p₃ ∙ p₄) ◃∙ p₅ ◃∎
    → ! p₅ ◃∙ ! p₂ ◃∙ ! p₃ ◃∎ =ₛ ! p₁ ◃∙ ! p₄ ◃∎
  !-!-tri-rot idp idp idp idp e = =ₛ-in (ap (λ p → ! p ∙ idp) (! (=ₛ-out e)))

  {- Horizontal compositions -}

  infixr 80 _∙2_ _∙'2_

  _∙2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _∙2_ {p = idp} idp β = β

  _∙'2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙' q == p' ∙' q'
  _∙'2_ {q = idp} α idp = α

  idp∙2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙2 (idp {a = q}) == idp
  idp∙2idp idp idp = idp

  idp∙'2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙'2 (idp {a = q}) == idp
  idp∙'2idp idp idp = idp

module _ {i} {A : Type i} where

  ∙-assoc2-!-inv-l-aux2 : {x₁ x₂ x₃ x₄ : A} (p₀ : x₁ == x₂) (p₁ : x₃ == x₂) (p₂ : x₄ == x₂)
    → (p₀ ∙ idp ∙' ! p₁) ∙ p₁ ∙ idp ∙' ! p₂ == p₀ ∙ idp ∙' ! p₂
  ∙-assoc2-!-inv-l-aux2 p₀ idp idp = ∙-unit-r (p₀ ∙ idp)

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ∙-assoc2-!-inv-l-aux : {x z : A} {y w u : B} (p₃ : x == z) (p₀ : w == f x) (p₁ : y == f x) (p₂ : u == f z)
    → (p₀ ∙ idp ∙' ! p₁) ∙ p₁ ∙ ap f p₃ ∙' ! p₂ == p₀ ∙ ap f p₃ ∙' ! p₂
  ∙-assoc2-!-inv-l-aux idp p₀ p₁ p₂ = ∙-assoc2-!-inv-l-aux2 p₀ p₁ p₂ 

  ∙-assoc2-!-inv-l-aux-idp3 : {x z : A} (p : x == z)
    → idp == ∙-assoc2-!-inv-l-aux p idp idp idp
  ∙-assoc2-!-inv-l-aux-idp3 idp = idp

  ∙-assoc2-!-inv-l : {x z : A} {y w : B}
    (p₀ : w == f z) (p₁ : y == f x) (p₂ : z == x) (p₃ : x == z)
    → (p₀ ∙ ap f p₂ ∙' ! p₁) ∙ p₁ ∙ ap f p₃ ∙' ! p₀ == p₀ ∙ ap f (p₂ ∙ p₃) ∙' ! p₀
  ∙-assoc2-!-inv-l p₀ p₁ idp p₃ = ∙-assoc2-!-inv-l-aux p₃ p₀ p₁ p₀

{- Coherence -}

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : A → B} {g : B → C} where

  cmp-inv-l : {x y : A} (p : x == y) → ! (ap (g ∘ f) p) ∙ ap g (ap f p) == idp
  cmp-inv-l idp = idp

  cmp-inv-r : {x y : A} (p : x == y) → ap g (ap f p) ∙ (ap (g ∘ f) (! p)) == idp
  cmp-inv-r idp = idp

  cmp-inv-rid : {x y : A} (p : x == y) → idp == ap (g ∘ f) p ∙ ! (ap g (ap f p) ∙ idp)
  cmp-inv-rid idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} where

  fun-rid-inv1 : {x y : A} (p : x == y) →  ((ap f p ∙ idp) ∙ idp) ∙ ! (ap f p ∙ idp) == idp
  fun-rid-inv1 idp = idp

  fun-rid-inv2 : {x y : A} (p : x == y) → idp == (ap f p ∙ idp) ∙ ! (ap f (p ∙ idp) ∙ idp)
  fun-rid-inv2 idp = idp

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-∙' : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙' q) == ap f p ∙' ap f q
  ap-∙' p idp = idp

  ap-inv-canc : {x y : A} (p : x == y) {z : B} (q : f x == z)
    → (! (ap f p) ∙ q) ∙ ! (ap f (! p) ∙ q) == idp
  ap-inv-canc idp idp = idp

  trip-ap-inv-p : {x y : A} {p : x == y} {w z : B} {q : f x == w} {r : w == z}
    → ! r ∙ (! q ∙ ap f p) == ! (! (ap f p) ∙ q ∙ r)
  trip-ap-inv-p {p = idp} {q = idp} {r = idp} = idp

  trip-ap-inv : {x y : A} (p : x == y) {w z : B} (q : f x == w) (r : w == z)
    → ! r ◃∙ (! q ∙ ap f p) ◃∎ =ₛ ! (! (ap f p) ∙ q ∙ r) ◃∎
  trip-ap-inv idp idp idp = =ₛ-in idp

  ap-concat-drev : {x y z : A} {p : x == y} {q : x == z} {w : B} {r  : f z == w}
    → (ap f q ∙ r) ∙ ! (ap f (! p ∙ q) ∙ r) == ap f p
  ap-concat-drev {p = idp} {q = idp} {r = idp} = idp

module _ {i} {A : Type i} {x y : A} where

  path-canc-l : (p : x == y) (q : y == y) → p == p ∙ q → idp == q
  path-canc-l idp q e = e

  left-canc : {z : A} (p : x == y) {r : x =-= z} → r =ₛ p ◃∙ ! p ◃∙ ↯ r ◃∎
  left-canc idp = =ₛ-in idp

  trip-inv : {w z : A} {p : y == x} {q : y == z} {r : z == w} → ! r ∙ ! q ∙ p == ! (! p ∙ q ∙ r)
  trip-inv {p = idp} {q = idp} {r = idp} = idp

  RUnCoh : (q : x == y) →
    ! (∙-unit-r (! q)) ∙ ∙-unit-r (! q) ∙ ap ! (! (∙-unit-r q)) == ap ! (! (∙-unit-r q) ∙ idp)
  RUnCoh idp = idp

{-
Sometimes we need to restart a new section in order to have everything in the
previous one generalized.
-}
module _ {i} {A : Type i} where
  {- Whisker and horizontal composition for Eckmann-Hilton argument -}

  infixr 80 _∙ᵣ_ _⋆2_ _⋆'2_
  infixl 80 _∙ₗ_

  _∙ᵣ_ : {x y z : A} {p p' : x == y} (α : p == p') (q : y == z)
    → p ∙ q == p' ∙ q
  _∙ᵣ_ {p = p} {p' = p'} α idp = ∙-unit-r p ∙ α ∙ ! (∙-unit-r p')

  _∙ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
    → p ∙ q == p ∙ q'
  _∙ₗ_ {q = q} {q' = q'} idp β = β

  _⋆2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
         (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆2_ {p' = p'} {q = q} α β = (α ∙ᵣ q) ∙ (p' ∙ₗ β)

  _⋆'2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
          (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆'2_ {p = p} {q' = q'} α β = (p ∙ₗ β) ∙ (α ∙ᵣ q')

  ⋆2=⋆'2 : {x y z : A} {p p' : x == y} {q q' : y == z}
           (α : p == p') (β : q == q')
    → α ⋆2 β == α ⋆'2 β
  ⋆2=⋆'2 {p = idp} {q = idp} idp idp = idp

module _ {i} {A : Type i} where

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

  anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
    → (p ∙ q == p ∙ r → q == r)
  anti-whisker-left idp h = h

{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} where

  {- Dependent constant path -}

  idpᵈ : {x : A} {u : B x} → u == u [ B ↓ idp ]
  idpᵈ = idp

  {- Dependent opposite path -}

  !ᵈ : {x y : A} {p : x == y} {u : B x} {v : B y}
    → (u == v [ B ↓ p ] → v == u [ B ↓ (! p)])
  !ᵈ {p = idp} = !

  !ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (u == v [ B ↓ (! p) ] → v == u [ B ↓ p ])
  !ᵈ' {p = idp} = !

  !ᵈ-!ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (q : u == v [ B ↓ (! p) ])
    → !ᵈ (!ᵈ' q) == q
  !ᵈ-!ᵈ' {p = idp} idp = idp

  {- Dependent concatenation -}

  infixr 80 _∙ᵈ_ _∙'ᵈ_ _◃_ _▹_ _!◃_ _▹!_

  _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙ᵈ_ {p = idp} {p' = idp} q r = q ∙ r

  _◃_ = _∙ᵈ_

  infixr 5 _∙ᵈ=_
  _∙ᵈ=_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → {d₁ d₂ : u == v [ B ↓ p ]}
    → {e₁ e₂ : v == w [ B ↓ p' ]}
    → d₁ == d₂ → e₁ == e₂
    → d₁ ∙ᵈ e₁ == d₂ ∙ᵈ e₂
  _∙ᵈ=_ idp idp = idp

  ◃idp : {x : A} {v w : B x} (q : w == v)
    → q ◃ idp == q
  ◃idp idp = idp

  idp◃ : {x y : A} {p : x == y}
    {u : B x} {v : B y} (r : u == v [ B ↓ p ])
    → idp ◃ r == r
  idp◃ {p = idp} r = idp

  ∙ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} f₀₁ f₁₂ f₂₃ = ∙-assoc f₀₁ f₁₂ f₂₃

  infixr 80 _∙ᵈᵣ_
  infixl 80 _∙ᵈₗ_

  {- Dependent whiskering -}
  _∙ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    (q : b₁ == b₂ [ B ↓ f ])
    → p ∙ᵈ q == p' ∙ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (_∙ f) α ]
  _∙ᵈᵣ_ {α = idp} idp q = idp

  _∙ᵈₗ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {f : a₁ == a₂} {f' : a₁ == a₂}
    {α : f == f'}
    {q : b₁ == b₂ [ B ↓ f ]} {q' : b₁ == b₂ [ B ↓ f' ]}
    (p : b₀ == b₁ [ B ↓ e ])
    (β : q == q' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → p ∙ᵈ q == p ∙ᵈ q' [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (e ∙_) α ]
  _∙ᵈₗ_ {α = idp} q idp = idp

  _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ p ∙' p' ]
  _∙'ᵈ_ {p = idp} {p' = idp} q r = q ∙' r

  _▹_ = _∙'ᵈ_

  ∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙'ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙'ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙'-assoc

  ∙ᵈ-∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙∙'-assoc

  ∙ᵈ-∙'ᵈ-assoc' : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙∙'-assoc' e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc' {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙∙'-assoc'

  _∙'ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    (q : b₁ == b₂ [ B ↓ f ])
    → p ∙'ᵈ q == p' ∙'ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (_∙' f) α ]
  _∙'ᵈᵣ_ {α = idp} idp q = idp

  {- That’s not perfect, because [q] could be a dependent path. But in that case
     this is not well typed… -}
  idp▹ : {x : A} {v w : B x} (q : v == w)
    → idp ▹ q == q
  idp▹ idp = idp

  ▹idp : {x y : A} {p : x == y}
    {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → q ▹ idp == q
  ▹idp {p = idp} idp = idp

  ▹∙ᵈ-∙ᵈ◃-assoc : {a₀ a₁ a₂ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂}
    {b₀ : B a₀} {b₁ b₁' : B a₁} {b₂ : B a₂}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f' : b₁ == b₁') (f₁₂ : b₁' == b₂ [ B ↓ e₁₂ ])
    → (f₀₁ ▹ f') ∙ᵈ f₁₂ == f₀₁ ∙ᵈ (f' ◃ f₁₂)
  ▹∙ᵈ-∙ᵈ◃-assoc {e₀₁ = idp} {e₁₂ = idp} = ∙'∙-∙∙-assoc

  _▹!_ : {x y z : A} {p : x == y} {p' : z == y}
    {u : B x} {v : B y} {w : B z}
    → u == v [ B ↓ p ]
    → w == v [ B ↓ p' ]
    → u == w [ B ↓ p ∙' (! p') ]
  _▹!_ {p' = idp} q idp = q

  idp▹! : {x : A} {v w : B x} (q : w == v)
    → idp ▹! q == ! q
  idp▹! idp = idp

  _!◃_ : {x y z : A} {p : y == x} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → v == u [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (! p) ∙ p' ]
  _!◃_ {p = idp} idp q = q

  !◃idp :{x : A} {v w : B x} (q : v == w)
    → q !◃ idp == ! q
  !◃idp idp = idp

  {-
  This is some kind of dependent horizontal composition (used in [apd∙]).
  -}

  infixr 80 _∙2ᵈ_ _∙'2ᵈ_

  _∙2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙ r == q' ∙ r' [ (λ a → x a == z a) ↓ p ])
  _∙2ᵈ_ {p = idp} α β = α ∙2 β

  _∙'2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙' r == q' ∙' r' [ (λ a → x a == z a) ↓ p ])
  _∙'2ᵈ_ {p = idp} α β = α ∙'2 β

  {-
  [apd∙] reduces a term of the form [apd (λ a → q a ∙ r a) p], do not confuse it
  with [apd-∙] which reduces a term of the form [apd f (p ∙ q)].
  -}

  apd∙ : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙ r a) p == apd q p ∙2ᵈ apd r p
  apd∙ q r idp = ! (idp∙2idp (q _) (r _))

  apd∙' : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙' r a) p == apd q p ∙'2ᵈ apd r p
  apd∙' q r idp = ! (idp∙'2idp (q _) (r _))

module _ {i j} {A : Type i} {B : A → Type j} where

  {- right whiskering and vertical composition -}
  ∙ᵈᵣ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' e'' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]} {p'' : b₀ == b₁ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α' ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → (β ∙'ᵈ β') ∙ᵈᵣ q == (β ∙ᵈᵣ q) ∙'ᵈ (β' ∙ᵈᵣ q)
        [ (λ y → (p ∙ᵈ q) == (p'' ∙ᵈ q) [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (_∙ f) α α' ]
  ∙ᵈᵣ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

  {- left whiskering and vertical composition -}
  ∙ᵈₗ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {f : a₀ == a₁} {e e' e'' : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₁ == b₂ [ B ↓ e ]} {p' : b₁ == b₂ [ B ↓ e' ]} {p'' : b₁ == b₂ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α' ])
    → (q : b₀ == b₁ [ B ↓ f ])
    → q ∙ᵈₗ (β ∙'ᵈ β') == (q ∙ᵈₗ β) ∙'ᵈ (q ∙ᵈₗ β')
        [ (λ y → (q ∙ᵈ p) == (q ∙ᵈ p'') [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (f ∙_) α α' ]
  ∙ᵈₗ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

  {- Exchange -}

  abstract
    ▹-∙'2ᵈ : {x y z : Π A B}
      {a a' a'' : A} {p : a == a'} {p' : a' == a''}
      {q0 : x a == y a} {q0' : x a' == y a'}
      {r0 : y a == z a} {r0' : y a' == z a'}
      {q0'' : x a'' == y a''} {r0'' : y a'' == z a''}
      (q : q0 == q0' [ (λ a → x a == y a) ↓ p ])
      (r : r0 == r0' [ (λ a → y a == z a) ↓ p ])
      (s : q0' == q0'' [ (λ a → x a == y a) ↓ p' ])
      (t : r0' == r0'' [ (λ a → y a == z a) ↓ p' ])
      → (q ∙'2ᵈ r) ▹ (s ∙'2ᵈ t) == (q ▹ s) ∙'2ᵈ (r ▹ t)
    ▹-∙'2ᵈ {p = idp} {p' = idp} {q0} {.q0} {r0} {.r0} idp idp idp idp =
      ap (λ u → (idp {a = q0} ∙'2 idp {a = r0}) ∙' u) (idp∙'2idp q0 r0)
