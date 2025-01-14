{-# OPTIONS --without-K --rewriting  #-}

-- Identity system on A-maps formed by A-homotopy

open import lib.Basics
open import lib.types.Sigma

module lib.FTID where

module _ {i j} (A : Type i) (B : A → Type j) (a : A) (b : B a) where

  ID-sys : Type (lmax i j)
  ID-sys = (p : Σ A B) → (a , b) == p

  module _ {k} (P : (x : A) → (B x → Type k)) where

    depEval : ((x : A) → ((y : B x) → P x y)) → P a b
    depEval h = h a b

    module _ (s : ID-sys) where

      const-dp : (p : P a b) → transport (λ (x , y) → P x y) (s (a , b)) p == p
      const-dp p = transpFunEq lemma p where
        lemma : s (a , b) == idp
        lemma = Set-UIP (contr-is-set (has-level-in ((a , b) , s))) (s (a , b)) idp

      fib-pr-eq : (x : A) (y : B x) → P a b → P x y
      fib-pr-eq x y = transport (λ (x , y) → P x y) (s (x , y)) 

      ID-sys-ind : has-sec {f = depEval}
      ID-sys-ind = sect (λ z → (λ x → λ y →  fib-pr-eq x y z)) const-dp

ID-ind : ∀ {i j k} {A : Type i} {B : A → Type j} {a : A} {b : B a}
  {P : (x : A) → (B x → Type k)} (s : ID-sys A B a b)
  → has-sec {f = depEval A B a b P}
ID-ind {A = A} {B = B} {a = a} {b = b} {P = P} s = ID-sys-ind A B a b P s

module _ {i} {A : Type i} where

  ≃-tot-contr : is-contr (Σ (Type i) (λ B → A ≃ B))
  ≃-tot-contr = equiv-preserves-level (Σ-emap-r (λ B → ua-equiv ⁻¹)) {{pathfrom-is-contr A}}

  ≃-tot-cent : (r : Σ (Type i) (λ B → A ≃ B)) → (A , ide A) == r
  ≃-tot-cent r = contr-path ≃-tot-contr r

  equiv-induction-b : ∀ {k} (P : {B : Type i} → (A ≃ B → Type k))
    → P (ide A) → {B : Type i} (e : A ≃ B) → P e
  equiv-induction-b P r {B} e = ind (ID-ind {P = λ B → P {B}} ≃-tot-cent) r B e  

  equiv-induction-β : ∀ {k} {P : {B : Type i} → (A ≃ B → Type k)} → (r : P (ide A))
    → equiv-induction-b P r (ide A) == r
  equiv-induction-β r = ind-eq (ID-ind ≃-tot-cent) r

