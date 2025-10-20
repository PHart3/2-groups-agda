{-# OPTIONS --without-K --confluence-check --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NType2
open import lib.types.TLevel
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Pointed
open import lib.types.LoopSpace
open import lib.types.Paths
open import lib.wild-cats.Ptd-wc

module lib.types.Truncation where

module _ {i} where

  postulate  -- HIT
    Trunc : (n : ℕ₋₂) (A : Type i) → Type i
    [_] : {n : ℕ₋₂} {A : Type i} → A → Trunc n A
    instance Trunc-level : {n : ℕ₋₂} {A : Type i} → has-level n (Trunc n A)

  module TruncElim {n : ℕ₋₂} {A : Type i} {j} {P : Trunc n A → Type j}
    {{p : {x : Trunc n A} → has-level n (P x)}} (d : (a : A) → P [ a ]) where

    postulate  -- HIT
      f : Π (Trunc n A) P
      [_]-β : ∀ a → f [ a ] ↦ d a
    {-# REWRITE [_]-β #-}

open TruncElim public renaming (f to Trunc-elim)

module TruncRec {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {{p : has-level n B}}
  (d : A → B) where

  private
    module M = TruncElim {{λ {x} → p}} d

  f : Trunc n A → B
  f = M.f

open TruncRec public renaming (f to Trunc-rec)

module TruncRecType {i j} {n : ℕ₋₂} {A : Type i} (d : A → n -Type j) where

  open TruncRec {{n -Type-level j}} d public

  flattening-Trunc : Σ (Trunc (S n) A) (fst ∘ f) ≃ Trunc (S n) (Σ A (fst ∘ d))
  flattening-Trunc = equiv to from to-from from-to where

    to-aux : (x : Trunc (S n) A) → (fst (f x) → Trunc (S n) (Σ A (fst ∘ d)))
    to-aux = Trunc-elim (λ a b → [ (a , b) ])

    to : Σ (Trunc (S n) A) (fst ∘ f) → Trunc (S n) (Σ A (fst ∘ d))
    to (x , y) = to-aux x y

    from-aux : Σ A (fst ∘ d) → Σ (Trunc (S n) A) (fst ∘ f)
    from-aux (a , b) = ([ a ] , b)

    from : Trunc (S n) (Σ A (fst ∘ d)) → Σ (Trunc (S n) A) (fst ∘ f)
    from = Trunc-rec {{Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))}}
                     from-aux

    to-from : (x : Trunc (S n) (Σ A (fst ∘ d))) → to (from x) == x
    to-from = Trunc-elim (λ _ → idp)

    from-to-aux : (a : Trunc (S n) A) (b : fst (f a)) → from (to-aux a b) == (a , b)
    from-to-aux = Trunc-elim {{Π-level (λ _ → =-preserves-level (Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))))}}
                             (λ a b → idp)

    from-to : (x : Σ (Trunc (S n) A) (fst ∘ f)) → from (to x) == x
    from-to (a , b) = from-to-aux a b


⊙Trunc : ∀ {i} → ℕ₋₂ → Ptd i → Ptd i
⊙Trunc n ⊙[ A , a ] = ⊙[ Trunc n A , [ a ] ]

[_]-⊙ : ∀ {i} {n} {X : Ptd i} → X ⊙→ ⊙Trunc n X
[_]-⊙ = [_] , idp

module ⊙TruncRec {i j} {n : ℕ₋₂} {A : Ptd i} {B : Ptd j} {{p : has-level n (de⊙ B)}}
  (d : A ⊙→ B) where

  private
    module M = TruncElim {{λ {x} → p}} (fst d)

  f : ⊙Trunc n A ⊙→ B
  f = M.f , snd d

open ⊙TruncRec public renaming (f to ⊙Trunc-rec)

module _ {i} {A : Type i} where

  [_]₀ : A → Trunc 0 A
  [_]₀ = [_] {n = 0}

  [_]₁ : A → Trunc 1 A
  [_]₁ = [_] {n = 1}

  [_]₂ : A → Trunc 2 A
  [_]₂ = [_] {n = 2}

module _ {i} {n : ℕ₋₂} {A : Type i} where

  private
    Trunc= : (a b : Trunc (S n) A) → n -Type i
    Trunc= = Trunc-elim (λ a → Trunc-elim ((λ b → (Trunc n (a == b) , Trunc-level))))

  {- t is for truncated -}
  _=ₜ_ : (a b : Trunc (S n) A) → Type i
  _=ₜ_ a b = fst (Trunc= a b)

  =ₜ-level : (a b : Trunc (S n) A) → has-level n (a =ₜ b)
  =ₜ-level a b = snd (Trunc= a b)

  =ₜ-refl : (a : Trunc (S n) A) → a =ₜ a
  =ₜ-refl = Trunc-elim {{λ {x} → raise-level _ (=ₜ-level x x)}}
                       (λ a → [ idp ])

  =ₜ-equiv : (a b : Trunc (S n) A) → (a == b) ≃ (a =ₜ b)
  =ₜ-equiv a b = to a b , to-is-equiv a b module =ₜ-maps where

    to : (a b : Trunc (S n) A) → (a == b → a =ₜ b)
    to a .a idp = =ₜ-refl a

    from-aux : (a b : A) → a == b → [ a ] == [ b ] :> Trunc (S n) A
    from-aux _ _ = ap [_]

    from : (a b : Trunc (S n) A) → a =ₜ b → a == b
    from = Trunc-elim (λ a → Trunc-elim (λ b → Trunc-rec (from-aux a b)))

    to-from-aux : (a b : A) → (p : a == b) → to _ _ (from-aux a b p) == [ p ]
    to-from-aux a .a idp = idp

    to-from : (a b : Trunc (S n) A) (x : a =ₜ b) → to a b (from a b x) == x
    to-from = Trunc-elim {{λ {x} → Π-level (λ y → Π-level (λ _ → =-preserves-level (raise-level _ (=ₜ-level x y))))}}
              (λ a → Trunc-elim {{λ {x} → Π-level (λ _ → =-preserves-level (raise-level _ (=ₜ-level [ a ] x)))}}
              (λ b → Trunc-elim
              (to-from-aux a b)))

    from-to-aux : (a : Trunc (S n) A) → from a a (=ₜ-refl a) == idp
    from-to-aux = Trunc-elim (λ _ → idp)

    from-to : (a b : Trunc (S n) A) (p : a == b) → from a b (to a b p) == p
    from-to a .a idp = from-to-aux a

    adj : (ta tb : Trunc (S n) A) (p : ta == tb)
      → ap (to ta tb) (from-to ta tb p) == to-from ta tb (to ta tb p)
    adj ta .ta idp =
      Trunc-elim {P = λ ta → ap (to ta ta) (from-to ta ta idp) == to-from ta ta (to ta ta idp)}
                 {{λ {x} → =-preserves-level $ =-preserves-level $ raise-level _ $ =ₜ-level x x}}
                 (λ _ → idp)
                 ta

    to-is-equiv : ∀ a b → is-equiv (to a b)
    to-is-equiv a b =
      record
      { g = from a b
      ; f-g = to-from a b
      ; g-f = from-to a b
      ; adj = adj a b
      }

  =ₜ-path : (a b : Trunc (S n) A) → (a == b) == (a =ₜ b)
  =ₜ-path a b = ua (=ₜ-equiv a b)

=ₜ-equiv-can : ∀ {i} (n : ℕ₋₂) {A : Type i} {a b : A}
  → ([ a ] == [ b ]) ≃ (Trunc n (a == b))
=ₜ-equiv-can _ {a = a} {b} = =ₜ-equiv [ a ] [ b ]

=ₜ-equiv-ind : ∀ {i j} {n : ℕ₋₂} {A : Type i} {a b : A} {P : [ a ] == [ b ] → Type j}
  → (s : (x : Trunc n (a == b)) → P (<– (=ₜ-equiv-can n) x))
  → (x : [ a ] == [ b ]) → P x
=ₜ-equiv-ind {n = n} {P = P} s x =
  transport P (<–-inv-l (=ₜ-equiv-can n) x) (s (–> (=ₜ-equiv-can n) x)) 

module _ {i} (A : Ptd i) {n : ℕ₋₂} where

  ⊙Ω-Trunc-[_]-≃ : ⊙Ω (⊙Trunc (S n) A) ⊙≃ ⊙Trunc n (⊙Ω A)
  ⊙Ω-Trunc-[_]-≃ = ≃-to-⊙≃ (=ₜ-equiv-can n) idp

  ⊙Ω-Trunc-[_] : ⊙Ω (⊙Trunc (S n) A) ⊙→ ⊙Trunc n (⊙Ω A)
  ⊙Ω-Trunc-[_] = ⊙–> ⊙Ω-Trunc-[_]-≃

  ⊙Ω-UnTrunc-[_] : ⊙Trunc n (⊙Ω A) ⊙→ ⊙Ω (⊙Trunc (S n) A)
  ⊙Ω-UnTrunc-[_] = ⊙<– ⊙Ω-Trunc-[_]-≃

{- Universal property -}

abstract
  Trunc-rec-is-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
    {{p : has-level n B}} → is-equiv (Trunc-rec {{p}} :> ((A → B) → (Trunc n A → B)))
  Trunc-rec-is-equiv n A B {{p}} = is-eq _ (λ f → f ∘ [_])
    (λ f → λ= (Trunc-elim (λ a → idp))) (λ f → idp)

Trunc-preserves-level : ∀ {i} {A : Type i} {n : ℕ₋₂} (m : ℕ₋₂)
 → has-level n A → has-level n (Trunc m A)
Trunc-preserves-level {n = ⟨-2⟩} _ p = has-level-in
  ([ contr-center p ] , Trunc-elim (λ a → ap [_] (contr-path p a)))
Trunc-preserves-level ⟨-2⟩ _ = contr-has-level Trunc-level
Trunc-preserves-level {n = (S n)} (S m) c = has-level-in (λ t₁ t₂ →
  Trunc-elim
    {{λ {s₁} → prop-has-level-S {A = has-level n (s₁ == t₂)} has-level-is-prop}}
    (λ a₁ → Trunc-elim
      {{λ {s₂} → prop-has-level-S {A = has-level n ([ a₁ ] == s₂)} has-level-is-prop}}
      (λ a₂ → equiv-preserves-level
      ((=ₜ-equiv [ a₁ ] [ a₂ ])⁻¹)
               {{Trunc-preserves-level {n = n} m (has-level-apply c a₁ a₂)}})
              t₂)
    t₁)

{- an n-type is equivalent to its n-truncation -}
unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (A : Type i)
  {{_ : has-level n A}} → Trunc n A ≃ A
unTrunc-equiv A {{pA}} = equiv f [_] (λ _ → idp) g-f where
  f = Trunc-rec {{pA}} (idf _)
  g-f = Trunc-elim {{=-preserves-level Trunc-level}} (λ _ → idp)

⊙unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (X : Ptd i)
  {{_ : has-level n (de⊙ X)}} → ⊙Trunc n X ⊙≃ X
⊙unTrunc-equiv {n = n} X = ≃-to-⊙≃ (unTrunc-equiv (de⊙ X)) idp

-- Equivalence associated to the universal property
Trunc-extend-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
  {{p : has-level n B}} → (A → B) ≃ (Trunc n A → B)
Trunc-extend-equiv n A B = (Trunc-rec , Trunc-rec-is-equiv n A B)

{- Various functorial properties -}

Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} → ((A → B) → (Trunc n A → Trunc n B))
Trunc-fmap f = Trunc-rec ([_] ∘ f)

⊙Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} → ((X ⊙→ Y) → (⊙Trunc n X ⊙→ ⊙Trunc n Y))
⊙Trunc-fmap F = Trunc-fmap (fst F) , ap [_] (snd F)

Trunc-Σ : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : A → Type j} → Trunc n (Σ A B) ≃ Trunc n (Σ A (Trunc n ∘ B))
Trunc-Σ {n = n} {A} {B} = equiv to from rt1 rt2
  where

    to : Trunc n (Σ A B) → Trunc n (Σ A (Trunc n ∘ B))
    to = Trunc-fmap (Σ-fmap-r (λ _ → [_]))

    from : Trunc n (Σ A (Trunc n ∘ B)) → Trunc n (Σ A B)
    from = Trunc-rec (uncurry λ x → Trunc-fmap λ y → x , y)

    rt1 : (x : Trunc n (Σ A (Trunc n ∘ B))) → to (from x) == x
    rt1 = Trunc-elim (uncurry λ x → Trunc-elim λ _ → idp)

    rt2 : (x : Trunc n (Σ A B)) → from (to x) == x
    rt2 = Trunc-elim λ _ → idp

module _ {i j} {A : Ptd i} {B : Ptd j} {n : ℕ₋₂} {{_ : has-level (S n) (de⊙ B)}} where

  ⊙Ω-Trunc-rec-coh-rot : (f : A ⊙→ B) →
    ⊙Trunc-fmap {n = n} (⊙Ω-fmap f) == [_]-⊙ ⊙∘ ⊙Ω-fmap (⊙Trunc-rec {n = S n} f) ⊙∘ ⊙Ω-UnTrunc-[_] A
  ⊙Ω-Trunc-rec-coh-rot (f₀ , idp) = ⊙-crd∼-to-== ((Trunc-elim λ p → ap [_] (ap-∘ (Trunc-elim f₀) [_] p)) , idp)

  ⊙Ω-Trunc-rec-coh : (f : A ⊙→ B) →
    ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ ⊙Trunc-fmap {n = n} (⊙Ω-fmap f) ⊙∘ ⊙Ω-Trunc-[ A ] == ⊙Ω-fmap (⊙Trunc-rec {n = S n} f)
  ⊙Ω-Trunc-rec-coh f = 
    ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ ⊙Trunc-fmap {n = n} (⊙Ω-fmap f) ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ m ⊙∘ ⊙Ω-Trunc-[_] A) (⊙Ω-Trunc-rec-coh-rot f) ⟩
    ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ ([_]-⊙ ⊙∘ ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ]) ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ m) (⊙λ= (⊙∘-assoc [_]-⊙ (⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ]) ⊙Ω-Trunc-[ A ])) ⟩
    ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ [_]-⊙ ⊙∘ (⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ]) ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ [_]-⊙ ⊙∘ m) (⊙λ= (⊙∘-assoc (⊙Ω-fmap (⊙Trunc-rec f)) ⊙Ω-UnTrunc-[ A ] ⊙Ω-Trunc-[ A ])) ⟩
    ⊙–> (⊙unTrunc-equiv (⊙Ω B)) ⊙∘ [_]-⊙ ⊙∘ ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ! (⊙λ= (⊙∘-assoc (⊙–> (⊙unTrunc-equiv (⊙Ω B))) [_]-⊙ (⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]))) ⟩
    (⊙–> (⊙unTrunc-equiv {n = n} (⊙Ω B)) ⊙∘ [_]-⊙) ⊙∘ ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ap (λ m → m ⊙∘ ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]) (⊙λ= (⊙<–-inv-r (⊙unTrunc-equiv {n = n} (⊙Ω B)))) ⟩
    ⊙idf (⊙Ω B) ⊙∘ ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ! (⊙-crd∼-to-== (⊙∘-lunit (⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]))) ⟩
    ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ ⊙Ω-UnTrunc-[ A ] ⊙∘ ⊙Ω-Trunc-[ A ]
      =⟨ ap (λ m → ⊙Ω-fmap (⊙Trunc-rec f) ⊙∘ m) (⊙λ= (⊙<–-inv-l (⊙Ω-Trunc-[ A ]-≃))) ⟩
    ⊙Ω-fmap (⊙Trunc-rec f) =∎

-- naturality of [_]-⊙ and its inverse

⊙-Trunc-fmap-nat : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) →
  ⊙Trunc-fmap {n = n} f ⊙∘ [_]-⊙ == [_]-⊙ ⊙∘ f
⊙-Trunc-fmap-nat f = ⊙λ= ((λ _ → idp) , (! (∙-unit-r (ap [_] (snd f)))))

⊙-unTrunc-fmap-nat-rot-in : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} {{_ : has-level n (de⊙ Y)}}
  (f : X ⊙→ Y) → f == ⊙–> (⊙unTrunc-equiv Y) ⊙∘ ⊙Trunc-fmap {n = n} f ⊙∘ [_]-⊙
⊙-unTrunc-fmap-nat-rot-in {X = X} {Y} f =
  f
    =⟨ ⊙-crd∼-to-== (⊙∘-lunit f) ⟩
  ⊙idf Y ⊙∘ f
    =⟨ ap (λ m → m ⊙∘ f) (! (⊙λ= (⊙<–-inv-r (⊙unTrunc-equiv Y)))) ⟩
  (⊙–> (⊙unTrunc-equiv Y) ⊙∘ [_]-⊙) ⊙∘ f
    =⟨ ⊙λ= (⊙∘-assoc (⊙–> (⊙unTrunc-equiv Y)) [_]-⊙ f) ⟩
  ⊙–> (⊙unTrunc-equiv Y) ⊙∘ [_]-⊙ ⊙∘ f
    =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv Y) ⊙∘ m) (! (⊙-Trunc-fmap-nat f)) ⟩
  ⊙–> (⊙unTrunc-equiv Y) ⊙∘ ⊙Trunc-fmap f ⊙∘ [_]-⊙ =∎

⊙-unTrunc-fmap-nat-rot-out : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} {{_ : has-level n (de⊙ X)}} (f : X ⊙→ Y)
  → ⊙Trunc-fmap {n = n} f == [_]-⊙ ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv X)
⊙-unTrunc-fmap-nat-rot-out {n = n} {X} f = 
  ⊙Trunc-fmap f
    =⟨ ap (λ m → ⊙Trunc-fmap f ⊙∘ m) (! (⊙λ= (⊙<–-inv-l (⊙unTrunc-equiv X)))) ⟩
  ⊙Trunc-fmap f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv X)
    =⟨ ! (⊙λ= (⊙∘-assoc (⊙Trunc-fmap f) [_]-⊙ (⊙–> (⊙unTrunc-equiv X)))) ⟩
  (⊙Trunc-fmap f ⊙∘ [_]-⊙) ⊙∘ ⊙–> (⊙unTrunc-equiv X)
    =⟨ ap (λ m → m ⊙∘ ⊙–> (⊙unTrunc-equiv X)) (⊙-Trunc-fmap-nat f) ⟩
  ([_]-⊙ ⊙∘ f) ⊙∘ ⊙–> (⊙unTrunc-equiv X)
    =⟨ ⊙λ= (⊙∘-assoc [_]-⊙ f (⊙–> (⊙unTrunc-equiv X))) ⟩
  [_]-⊙ ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv X) =∎

⊙-unTrunc-fmap-nat : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} {{_ : has-level n (de⊙ X)}} {{_ : has-level n (de⊙ Y)}}
  (f : X ⊙→ Y) → ⊙–> (⊙unTrunc-equiv Y) ⊙∘ ⊙Trunc-fmap {n = n} f == f ⊙∘ ⊙–> (⊙unTrunc-equiv X)
⊙-unTrunc-fmap-nat {X = X} {Y} f =
  ap (λ m → ⊙–> (⊙unTrunc-equiv Y) ⊙∘ m) (⊙-unTrunc-fmap-nat-rot-out f) ∙
  ! (⊙λ= (⊙∘-assoc (⊙–> (⊙unTrunc-equiv Y)) [_]-⊙ (f ⊙∘ ⊙–> (⊙unTrunc-equiv X)))) ∙
  ap (λ m → m ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv X)) (⊙λ= (⊙<–-inv-r (⊙unTrunc-equiv Y))) ∙
  ! (⊙-crd∼-to-== (⊙∘-lunit (f ⊙∘ ⊙–> (⊙unTrunc-equiv X))))

Trunc-fmap2 : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → ((A → B → C) → (Trunc n A → Trunc n B → Trunc n C))
Trunc-fmap2 f = Trunc-rec (λ a → Trunc-fmap (f a))

Trunc-fpmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {f g : A → B}
  → f ∼ g → Trunc-fmap {n = n} f ∼ Trunc-fmap g
Trunc-fpmap h = Trunc-elim (ap [_] ∘ h)

Trunc-fmap-idf : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → ∀ x → Trunc-fmap {n = n} (idf A) x == x
Trunc-fmap-idf =
  Trunc-elim (λ _ → idp)

Trunc-fmap-∘ : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → (g : B → C) → (f : A → B)
  → ∀ x → Trunc-fmap {n = n} g (Trunc-fmap f x) == Trunc-fmap (g ∘ f) x
Trunc-fmap-∘ g f =
  Trunc-elim (λ _ → idp)

⊙Trunc-fmap-idf : ∀ {i} {n : ℕ₋₂} (A : Ptd i)
  → ⊙Trunc-fmap {n = n} (⊙idf A) == ⊙idf (⊙Trunc n A)
⊙Trunc-fmap-idf A = ⊙λ= (Trunc-fmap-idf {A = de⊙ A} , idp)

⊙Trunc-fmap-∘ : ∀ {i j k} {n : ℕ₋₂} {A : Ptd i} {B : Ptd j} {C : Ptd k}
  → (g : B ⊙→ C) (f : A ⊙→ B)
  → ⊙Trunc-fmap {n = n} g ⊙∘ ⊙Trunc-fmap f == ⊙Trunc-fmap (g ⊙∘ f)
⊙Trunc-fmap-∘ g f = ⊙λ= ((Trunc-fmap-∘ (fst g) (fst f)) ,
  (ap (λ p → p ∙ ap [_] (snd g)) (∘-ap (Trunc-elim (λ x → [ fst g x ])) [_] (snd f)) ∙
  ! (ap-∘-∙ [_] (fst g) (snd f) (snd g))))

⊙Trunc-∘-tri : ∀ {i j k l} {n : ℕ₋₂} {W : Ptd l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (k : Z ⊙→ W) (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Trunc-fmap k ⊙∘ ⊙Trunc-fmap g ⊙∘ ⊙Trunc-fmap f == ⊙Trunc-fmap {n = n} (k ⊙∘ g ⊙∘ f)
⊙Trunc-∘-tri k g f = ap (λ m → ⊙Trunc-fmap k ⊙∘ m) (⊙Trunc-fmap-∘ g f) ∙ ⊙Trunc-fmap-∘ k (g ⊙∘ f)

-- ⊙Trunc as wild functor
⊙Trunc-wf : ∀ {n : ℕ₋₂} {i} → PtdFunctor i i
obj (⊙Trunc-wf {n}) = ⊙Trunc n
arr (⊙Trunc-wf {n}) = ⊙Trunc-fmap
id (⊙Trunc-wf {n}) = ⊙Trunc-fmap-idf
comp (⊙Trunc-wf {n}) f g = ! (⊙Trunc-fmap-∘ g f)

⊙Trunc-fmap-≃ : ∀ {i n} {X Y : Ptd i} → X ⊙≃ Y → ⊙Trunc n X ⊙≃ ⊙Trunc n Y
⊙Trunc-fmap-≃ e = ⊙≃-from-equiv-wc (F-equiv-wc (⊙Trunc-wf) (⊙≃-to-equiv-wc e))

Trunc-csmap : ∀ {i₀ i₁ j₀ j₁} {n : ℕ₋₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f : A₀ → B₀} {g : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f g hA hB
  → CommSquare (Trunc-fmap {n = n} f) (Trunc-fmap g) (Trunc-fmap hA) (Trunc-fmap hB)
Trunc-csmap (comm-sqr cs) = comm-sqr $ Trunc-elim (ap [_] ∘ cs)

transport-Trunc : ∀ {i j} {A : Type i} {n : ℕ₋₂} (P : A → Type j)
  {x y : A} (p : x == y) (b : P x)
  → transport (Trunc n ∘ P) p [ b ] == [ transport P p b ]
transport-Trunc _ idp _ = idp

{- Truncation preserves equivalences - more convenient than univalence+ap
 - when we need to know the forward or backward function explicitly -}
module _ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} where

  Trunc-isemap : {f : A → B} → is-equiv f → is-equiv (Trunc-fmap {n = n} f)
  Trunc-isemap {f-orig} ie = is-eq f g f-g g-f where
    f = Trunc-fmap f-orig
    g = Trunc-fmap (is-equiv.g ie)

    f-g : ∀ tb → f (g tb) == tb
    f-g = Trunc-elim (ap [_] ∘ is-equiv.f-g ie)

    g-f : ∀ ta → g (f ta) == ta
    g-f = Trunc-elim (ap [_] ∘ is-equiv.g-f ie)

  Trunc-emap : A ≃ B → Trunc n A ≃ Trunc n B
  Trunc-emap (f , f-ie) = Trunc-fmap f , Trunc-isemap f-ie

-- n-truncation on n-types is fully faithful
module _ {i j} {n : ℕ₋₂} {A : Ptd i} {B : Ptd j} {{_ : has-level n (de⊙ A)}} {{_ : has-level n (de⊙ B)}} where

  abstract

    ⊙Trunc-ff : is-equiv (⊙Trunc-fmap {n = n} {A} {B})
    ⊙Trunc-ff = is-eq ⊙Trunc-fmap (λ f →  ⊙–> (⊙unTrunc-equiv B) ⊙∘ f ⊙∘ [_]-⊙)
      (λ f → ⊙-unTrunc-fmap-nat-rot-out (⊙–> (⊙unTrunc-equiv B) ⊙∘ f ⊙∘ [_]-⊙) ∙
        ([_]-⊙ ⊙∘ (⊙–> (⊙unTrunc-equiv B) ⊙∘ f ⊙∘ [_]-⊙) ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ap (λ m → [_]-⊙ ⊙∘ m) (⊙λ= (⊙∘-assoc (⊙–> (⊙unTrunc-equiv B)) (f ⊙∘ [_]-⊙) (⊙–> (⊙unTrunc-equiv A)))) ⟩
        [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv B) ⊙∘ (f ⊙∘ [_]-⊙) ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ap (λ m → [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv B) ⊙∘ m) (⊙λ= (⊙∘-assoc f [_]-⊙ (⊙–> (⊙unTrunc-equiv A)))) ⟩
        [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv B) ⊙∘ f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ! (⊙λ= (⊙∘-assoc [_]-⊙ (⊙–> (⊙unTrunc-equiv B)) (f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)))) ⟩
        ([_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv B)) ⊙∘ f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ap (λ m → m ⊙∘ f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)) (⊙λ= (⊙<–-inv-l (⊙unTrunc-equiv B))) ⟩
        ⊙idf (⊙Trunc n B) ⊙∘ f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ! (⊙-crd∼-to-== (⊙∘-lunit (f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)))) ⟩
        f ⊙∘ [_]-⊙ ⊙∘ ⊙–> (⊙unTrunc-equiv A)
          =⟨ ap (λ m → f ⊙∘ m) (⊙λ= (⊙<–-inv-l (⊙unTrunc-equiv A))) ⟩
        f =∎))
      λ f → ap (λ m → ⊙–> (⊙unTrunc-equiv B) ⊙∘ m ⊙∘ [_]-⊙) (⊙-unTrunc-fmap-nat-rot-out f) ∙
        (⊙–> (⊙unTrunc-equiv B) ⊙∘ ([_]-⊙ ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv A)) ⊙∘ [_]-⊙
          =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv B) ⊙∘ m) (⊙λ= (⊙∘-assoc [_]-⊙ (f ⊙∘ ⊙–> (⊙unTrunc-equiv A)) [_]-⊙)) ⟩
        ⊙–> (⊙unTrunc-equiv B) ⊙∘ [_]-⊙ ⊙∘ (f ⊙∘ ⊙–> (⊙unTrunc-equiv A)) ⊙∘ [_]-⊙
          =⟨ ap (λ m → ⊙–> (⊙unTrunc-equiv B) ⊙∘ [_]-⊙ ⊙∘ m) (⊙λ= (⊙∘-assoc f (⊙–> (⊙unTrunc-equiv A))  [_]-⊙)) ⟩
        ⊙–> (⊙unTrunc-equiv B) ⊙∘ [_]-⊙ ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙
          =⟨ ! (⊙λ= (⊙∘-assoc (⊙–> (⊙unTrunc-equiv B)) [_]-⊙ (f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙))) ⟩
        (⊙–> (⊙unTrunc-equiv B) ⊙∘ [_]-⊙) ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙
          =⟨ ap (λ m → m ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙) (⊙λ= (⊙<–-inv-r (⊙unTrunc-equiv B))) ⟩
        ⊙idf B ⊙∘ f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙
          =⟨ ! (⊙-crd∼-to-== (⊙∘-lunit (f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙ ))) ⟩
        f ⊙∘ ⊙–> (⊙unTrunc-equiv A) ⊙∘ [_]-⊙
          =⟨ ap (λ m → f ⊙∘ m) (⊙λ= (⊙<–-inv-r (⊙unTrunc-equiv A))) ⟩
        f =∎)

    ⊙Trunc-fmap-inj : {f g : A ⊙→ B} → ⊙Trunc-fmap {n = n} f == ⊙Trunc-fmap g → f == g
    ⊙Trunc-fmap-inj {f} {g} = equiv-is-inj ⊙Trunc-ff f g

Trunc-fuse : ∀ {i} (A : Type i) (m n : ℕ₋₂)
  → Trunc m (Trunc n A) ≃ Trunc (minT m n) A
Trunc-fuse A m n = equiv
  (Trunc-rec {{raise-level-≤T (minT≤l m n) Trunc-level}}
    (Trunc-rec {{raise-level-≤T (minT≤r m n) Trunc-level}}
      [_]))
  (Trunc-rec ([_] ∘ [_]))
  (Trunc-elim (λ _ → idp))
  (Trunc-elim (Trunc-elim
       {{=-preserves-level (Trunc-preserves-level _ Trunc-level)}}
       (λ _ → idp)))
  where
      instance
        l : has-level (minT m n) (Trunc m (Trunc n A))
        l with (minT-out m n)
        l | inl p = transport (λ k → has-level k (Trunc m (Trunc n A)))
                              (! p) Trunc-level
        l | inr q = Trunc-preserves-level _
                      (transport (λ k → has-level k (Trunc n A))
                                 (! q) Trunc-level)

Trunc-fuse-≤ : ∀ {i} (A : Type i) {m n : ℕ₋₂} (m≤n : m ≤T n)
  → Trunc m (Trunc n A) ≃ Trunc m A
Trunc-fuse-≤ A m≤n = equiv
  (Trunc-rec (Trunc-rec {{raise-level-≤T m≤n Trunc-level}}
      [_]))
  (Trunc-rec ([_] ∘ [_]))
  (Trunc-elim (λ _ → idp))
  (Trunc-elim (Trunc-elim
       {{=-preserves-level (Trunc-preserves-level _ Trunc-level)}}
       (λ _ → idp)))

{- Pushing concatenatation through _=ₜ_ -}
module _ {i} {n : ℕ₋₂} {A : Type i} where

  {- concatenation in _=ₜ_ -}
  infixr 80 _∙ₜ_ 
  _∙ₜ_ : {ta tb tc : Trunc (S n) A}
    → ta =ₜ tb → tb =ₜ tc → ta =ₜ tc
  _∙ₜ_ {ta = ta} {tb = tb} {tc = tc} =
    Trunc-elim {P = λ ta → C ta tb tc}
      {{λ {ta} → level ta tb tc}}
      (λ a → Trunc-elim {P = λ tb → C [ a ] tb tc}
         {{λ {tb} → level [ a ] tb tc}}
         (λ b → Trunc-elim {P = λ tc → C [ a ] [ b ] tc}
                  {{λ {tc} → level [ a ] [ b ] tc}}
                  (λ c → Trunc-fmap2 _∙_)
                  tc)
         tb)
      ta
    where
    C : (ta tb tc : Trunc (S n) A) → Type i
    C ta tb tc = ta =ₜ tb → tb =ₜ tc → ta =ₜ tc
    level : (ta tb tc : Trunc (S n) A) → has-level (S n) (C ta tb tc)
    level ta tb tc = raise-level _ $
              Π-level (λ _ → Π-level (λ _ → =ₜ-level ta tc))

  ∙ₜ-lunit : {ta tb : Trunc (S n) A} (u : ta =ₜ tb) → _∙ₜ_ {ta = ta} {ta} {tb} (=ₜ-refl ta) u == u
  ∙ₜ-lunit {ta} {tb} = Trunc-elim {P = λ ta → (u : ta =ₜ tb) → _∙ₜ_ {ta = ta} {ta} {tb} (=ₜ-refl ta) u == u}
    {{λ {x} → Π-level (λ u → raise-level n (=-preserves-level (=ₜ-level x tb)))}}
    (λ a → Trunc-elim {P = λ tb → (u : [ a ] =ₜ tb) → _∙ₜ_ {ta = [ a ]} {[ a ]} {tb} (=ₜ-refl [ a ]) u == u}
      {{λ {tb} → Π-level (λ u → raise-level n (=-preserves-level (=ₜ-level [ a ] tb)))}}
        (λ b u → Trunc-elim {P = λ u → _∙ₜ_ {ta = [ a ]} {[ a ]} {[ b ]} (=ₜ-refl [ a ]) u == u} (λ _ → idp) u) tb) ta

  ∙ₜ-assoc : {ta tb tc td : Trunc (S n) A}
    (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td)
    → _∙ₜ_ {ta} (_∙ₜ_ {ta} tp tq) tr
      == _∙ₜ_ {ta} tp (_∙ₜ_ {tb} tq tr)
  ∙ₜ-assoc {ta = ta} {tb = tb} {tc = tc} {td = td} =
    Trunc-elim {P = λ ta → C ta tb tc td}
      {{λ {ta} → C-level ta tb tc td}}
      (λ a → Trunc-elim {P = λ tb → C [ a ] tb tc td}
        {{λ {tb} → C-level [ a ] tb tc td}}
        (λ b → Trunc-elim {P = λ tc → C [ a ] [ b ] tc td}
          {{λ {tc} → C-level [ a ] [ b ] tc td}}
          (λ c → Trunc-elim {P = λ td → C [ a ] [ b ] [ c ] td}
            {{λ {td} → C-level [ a ] [ b ] [ c ] td}}
            (λ d tp tq tr → Trunc-elim
              {P = λ tp → D [ a ] [ b ] [ c ] [ d ] tp tq tr}
              {{λ {tp} → D-level [ a ] [ b ] [ c ] [ d ] tp tq tr}}
              (λ p → Trunc-elim
                {P = λ tq → D [ a ] [ b ] [ c ] [ d ] [ p ] tq tr}
                {{λ {tq} → D-level [ a ] [ b ] [ c ] [ d ] [ p ] tq tr}}
                (λ q → Trunc-elim
                  {P = λ tr → D [ a ] [ b ] [ c ] [ d ] [ p ] [ q ] tr}
                  {{λ {tr} → D-level [ a ] [ b ] [ c ] [ d ] [ p ] [ q ] tr}}
                  (λ r → ap [_] (∙-assoc p q r))
                  tr)
                tq)
              tp)
            td)
          tc)
        tb)
      ta
    where
    D : (ta tb tc td : Trunc (S n) A)
      → ta =ₜ tb → tb =ₜ tc → tc =ₜ td
      → Type i
    D ta tb tc td tp tq tr =
         _∙ₜ_ {ta} (_∙ₜ_ {ta} tp tq) tr
      == _∙ₜ_ {ta} tp (_∙ₜ_ {tb} tq tr)
    C : (ta tb tc td : Trunc (S n) A) → Type i
    C ta tb tc td = ∀ tp tq tr → D ta tb tc td tp tq tr
    D-level : (ta tb tc td : Trunc (S n) A)
      (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td)
      → has-level n (D ta tb tc td tp tq tr)
    D-level ta tb tc td tp tq tr = =-preserves-level (=ₜ-level ta td)
    C-level : (ta tb tc td : Trunc (S n) A) → has-level (S n) (C ta tb tc td)
    C-level ta tb tc td =
      raise-level _ $
      Π-level $ λ tp →
      Π-level $ λ tq →
      Π-level $ λ tr →
      D-level ta tb tc td tp tq tr

  abstract
    ∙ₜ-assoc-pentagon : {ta tb tc td te : Trunc (S n) A}
      (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td) (ts : td =ₜ te)
      → ∙ₜ-assoc {ta} (_∙ₜ_ {ta} tp tq) tr ts ◃∙
        ∙ₜ-assoc {ta} tp tq (_∙ₜ_ {tc} tr ts) ◃∎
        =ₛ
        ap (λ u → _∙ₜ_ {ta} u ts) (∙ₜ-assoc {ta} tp tq tr) ◃∙
        ∙ₜ-assoc {ta} tp (_∙ₜ_ {tb} tq tr) ts ◃∙
        ap (_∙ₜ_ {ta} tp) (∙ₜ-assoc {tb} tq tr ts) ◃∎
    ∙ₜ-assoc-pentagon {ta} {tb} {tc} {td} {te} = core ta tb tc td te
      where
      P : (ta tb tc td te : Trunc (S n) A)
        (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td) (ts : td =ₜ te)
        → Type i
      P ta tb tc td te tp tq tr ts =
        ∙ₜ-assoc {ta} (_∙ₜ_ {ta} tp tq) tr ts ◃∙
        ∙ₜ-assoc {ta} tp tq (_∙ₜ_ {tc} tr ts) ◃∎
        =ₛ
        ap (λ u → _∙ₜ_ {ta} u ts) (∙ₜ-assoc {ta} tp tq tr) ◃∙
        ∙ₜ-assoc {ta} tp (_∙ₜ_ {tb} tq tr) ts ◃∙
        ap (_∙ₜ_ {ta} tp) (∙ₜ-assoc {tb} tq tr ts) ◃∎
      P-level : ∀ ta tb tc td te →
        (tp : ta =ₜ tb) (tq : tb =ₜ tc) (tr : tc =ₜ td) (ts : td =ₜ te)
        → has-level n (P ta tb tc td te tp tq tr ts)
      P-level ta tb tc td te tp tq tr ts =
        =ₛ-level $ raise-level _ $ raise-level _ $ =ₜ-level ta te
      Q : (ta tb tc td te : Trunc (S n) A) → Type i
      Q ta tb tc td te = ∀ tp tq tr ts → P ta tb tc td te tp tq tr ts
      Q-level : ∀ ta tb tc td te → has-level (S n) (Q ta tb tc td te)
      Q-level ta tb tc td te =
        raise-level n $
        Π-level $ λ tp →
        Π-level $ λ tq →
        Π-level $ λ tr →
        Π-level $ λ ts →
        P-level ta tb tc td te tp tq tr ts
      core' : ∀ {a} {b} {c} {d} {e} p q r s → P [ a ] [ b ] [ c ] [ d ] [ e ] [ p ] [ q ] [ r ] [ s ]
      core' idp idp r s = =ₛ-in idp
      core : ∀ ta tb tc td te → Q ta tb tc td te
      core ta tb tc td te =
        Trunc-elim {P = λ ta → Q ta tb tc td te} {{λ {ta} → Q-level ta tb tc td te}} (λ a →
          Trunc-elim {P = λ tb → Q [ a ] tb tc td te} {{λ {tb} → Q-level [ a ] tb tc td te}} (λ b →
            Trunc-elim {P = λ tc → Q [ a ] [ b ] tc td te} {{λ {tc} → Q-level [ a ] [ b ] tc td te}} (λ c →
              Trunc-elim {P = λ td → Q [ a ] [ b ] [ c ] td te} {{λ {td} → Q-level [ a ] [ b ] [ c ] td te}} (λ d →
                Trunc-elim {P = λ te → Q [ a ] [ b ] [ c ] [ d ] te} {{λ {te} → Q-level [ a ] [ b ] [ c ] [ d ] te}} (λ e →
                  let R = P [ a ] [ b ] [ c ] [ d ] [ e ]
                      R-level = P-level [ a ] [ b ] [ c ] [ d ] [ e ]
                  in λ tp tq tr ts →
                  Trunc-elim {P = λ tp → R tp tq tr ts} {{λ {tp} → R-level tp tq tr ts}} (λ p →
                    Trunc-elim {P = λ tq → R [ p ] tq tr ts} {{λ {tq} → R-level [ p ] tq tr ts}} (λ q →
                      Trunc-elim {P = λ tr → R [ p ] [ q ] tr ts} {{λ {tr} → R-level [ p ] [ q ] tr ts}} (λ r →
                        Trunc-elim {P = λ ts → R [ p ] [ q ] [ r ] ts} {{λ {ts} → R-level [ p ] [ q ] [ r ] ts}} (λ s →
                          core' p q r s
                        ) ts
                      ) tr
                    ) tq
                  ) tp
                ) te
              ) td
            ) tc
          ) tb
        ) ta

  –>-=ₜ-equiv-pres-∙ : {ta tb tc : Trunc (S n) A}
    (p : ta == tb) (q : tb == tc)
    →  –> (=ₜ-equiv ta tc) (p ∙ q)
    == _∙ₜ_ {ta = ta} (–> (=ₜ-equiv ta tb) p) (–> (=ₜ-equiv tb tc) q)
  –>-=ₜ-equiv-pres-∙ {ta = ta} idp idp =
    Trunc-elim
      {P = λ ta → –> (=ₜ-equiv ta ta) idp
              == _∙ₜ_ {ta = ta} (–> (=ₜ-equiv ta ta) idp)
                                (–> (=ₜ-equiv ta ta) idp)}
      {{λ {ta} → raise-level _ $ =-preserves-level $ =ₜ-level ta ta}}
      (λ a → idp)
      ta

  abstract
    –>-=ₜ-equiv-pres-∙-coh : {ta tb tc td : Trunc (S n) A}
      (p : ta == tb) (q : tb == tc) (r : tc == td)
      → –>-=ₜ-equiv-pres-∙ (p ∙ q) r ◃∙
        ap (λ u → _∙ₜ_ {ta = ta} u (–> (=ₜ-equiv tc td) r)) (–>-=ₜ-equiv-pres-∙ p q) ◃∙
        ∙ₜ-assoc {ta = ta} (–> (=ₜ-equiv ta tb) p) (–> (=ₜ-equiv tb tc) q) (–> (=ₜ-equiv tc td) r) ◃∎
        =ₛ
        ap (–> (=ₜ-equiv ta td)) (∙-assoc p q r) ◃∙
        –>-=ₜ-equiv-pres-∙ p (q ∙ r) ◃∙
        ap (_∙ₜ_ {ta = ta} (–> (=ₜ-equiv ta tb) p)) (–>-=ₜ-equiv-pres-∙ q r) ◃∎
    –>-=ₜ-equiv-pres-∙-coh {ta = ta} idp idp idp =
      Trunc-elim
        {P = λ ta → P ta ta ta ta idp idp idp}
        {{λ {ta} → =ₛ-level $ raise-level (S (S n)) $ raise-level (S n) $ raise-level n $ =ₜ-level ta ta}}
        (λ a → =ₛ-in idp)
        ta
      where
      P : (ta tb tc td : Trunc (S n) A) (p : ta == tb) (q : tb == tc) (r : tc == td) → Type i
      P ta tb tc td p q r =
        –>-=ₜ-equiv-pres-∙ (p ∙ q) r ◃∙
        ap (λ u → _∙ₜ_ {ta = ta} u (–> (=ₜ-equiv tc td) r)) (–>-=ₜ-equiv-pres-∙ p q) ◃∙
        ∙ₜ-assoc {ta = ta} (–> (=ₜ-equiv ta tb) p) (–> (=ₜ-equiv tb tc) q) (–> (=ₜ-equiv tc td) r) ◃∎
        =ₛ
        ap (–> (=ₜ-equiv ta td)) (∙-assoc p q r) ◃∙
        –>-=ₜ-equiv-pres-∙ p (q ∙ r) ◃∙
        ap (_∙ₜ_ {ta = ta} (–> (=ₜ-equiv ta tb) p)) (–>-=ₜ-equiv-pres-∙ q r) ◃∎

-- interaction between higher loop spaces and particular fibers of [_]

module _ {i} {A : Type i} {x y : A} {a : A} {n : ℕ₋₂} {{_ : has-level (S (S (S n))) A}} where

  =Σ-econv-hfib-Trunc-aux1 : {u : [_] {n = S (S n)} x =ₜ [ a ]} {v : [ y ] =ₜ [ a ]} →
    ((x , u) == (y , v)) ≃ (Σ (x == y) (λ p → _∙ₜ_ {ta = [ x ]} {[ y ]} {[ a ]} ([_] {n = S n} p) v == u))
  =Σ-econv-hfib-Trunc-aux1 {u} {v} = equiv to (uncurry λ p h → from p {u' = u} h) (uncurry λ p h → from-to p {v} h) to-from
    where

      to : {c₁ c₂ : Σ A (λ z → [ z ] =ₜ [ a ])} →
        c₁ == c₂ → Σ (fst c₁ == fst c₂) (λ p → _∙ₜ_ {ta = [ fst c₁ ]} {[ fst c₂ ]} {[ a ]} [ p ] (snd c₂) == snd c₁)
      to {c₁} idp = idp , ∙ₜ-lunit {ta = [ fst c₁ ]} {[ a ]} (snd c₁)

      from : ∀ {z} (p : x == z) {q : [ z ] =ₜ [ a ]} {u' : [ x ] =ₜ [ a ]} → _∙ₜ_ {ta = [ x ]} {[ z ]} {[ a ]} [ p ] q == u' → (x , u') == (z , q)
      from {z} idp {q} e = pair= idp (! (! (∙ₜ-lunit {ta = [ z ]} {[ a ]} q) ∙ e))

      from-to : ∀ {z} (p : x == z) {q : [ z ] =ₜ [ a ]} (h : _∙ₜ_ {ta = [ x ]} {[ z ]} {[ a ]} [ p ] q == u)
        → to (from p {q} h) == (p , h)
      from-to idp {q} = Trunc-elim
        {P = λ q → (h : _∙ₜ_ {ta = [ x ]} {[ x ]} {[ a ]} [ idp ] q == u) → to (ap (x ,_) (! (! (∙ₜ-lunit {ta = [ x ]} {[ a ]} q) ∙ h))) == idp , h}
        {{Π-level λ h → has-level-apply-instance {{Σ-level ⟨⟩ λ p → has-level-apply-instance {{raise-level (S (S n)) (raise-level (S n) ⟨⟩)}}}}}}
        (λ q' → aux q') q
          where
            aux : ∀ q' {u'} (h : _∙ₜ_ {ta = [ x ]} {[ x ]} {[ a ]} [ idp ] [ q' ] == u') → to (ap (x ,_) (! h)) == idp , h
            aux q' idp = idp

      to-from : ∀ {c} (h : (x , u) == c) → uncurry (λ p h → from p h) (to h) == h
      to-from idp = Trunc-elim {P = λ u' → uncurry (λ p → from p {u'} {u'}) (idp , ∙ₜ-lunit {ta = [ x ]} {[ a ]} u') == idp}
        {{λ {u'} → has-level-apply-instance {{has-level-apply-instance {{Σ-level ⟨⟩ λ x → raise-level (S (S n)) (raise-level (S n) ⟨⟩)}}}}}}
        (λ _ → idp) u

  =Σ-econv-hfib-Trunc-aux2 : {u : x == a} {v : y == a} →
    (Σ (x == y) (λ p → _∙ₜ_ {ta = [ x ]} {[ y ]} {[ a ]} ([_] {n = S n} p) [ v ] == [ u ])) ≃ (Σ (x == y) (λ p → Trunc n (p == u ∙ ! v)))
  =Σ-econv-hfib-Trunc-aux2 {u} {v} = Σ-emap-r (λ p →
    Trunc-emap (pre∙-equiv (assoc-inv-r p v) ∘e ap-equiv (post∙-equiv (! v)) (p ∙ v) u) ∘e =ₜ-equiv-can n)
 
  =Σ-econv-hfib-Trunc : {u : x == a} {v : y == a} →
    ((x , [_] {n = S n} u) == (y , [ v ])) ≃ (Σ (x == y) (λ p → Trunc n (p == u ∙ ! v)))
  =Σ-econv-hfib-Trunc {u} {v} = =Σ-econv-hfib-Trunc-aux2 ∘e =Σ-econv-hfib-Trunc-aux1

⊙Ω-hfib-Trunc : ∀ {i} {n : ℕ} {X : Type i} {x : X} {{_ : has-level (S (S ⟨ n ⟩)) X}} →
  ⊙Ω ⊙[ Σ X (λ a → [_] {n = ⟨ S n ⟩} a == [ x ]) , (x , idp) ]
    ⊙≃
  ⊙[ Σ (x == x) (λ p → [_] {n = ⟨ n ⟩} p == [ idp ]) , (idp , idp) ]
⊙Ω-hfib-Trunc {n = n} {X} {x} = ≃-to-⊙≃
  (Σ-emap-r (λ _ → (=ₜ-equiv-can (S ⟨ n ⟩₋₂)) ⁻¹) ∘e
  =Σ-econv-hfib-Trunc {u = idp} {v = idp} ∘e
  Ω-emap {X = ⊙[ Σ X (λ a → [_] {n = ⟨ S n ⟩} a == [ x ]) , (x , idp) ]} (≃-to-⊙≃ (Σ-emap-r λ _ → =ₜ-equiv-can ⟨ n ⟩) idp))
  idp

Ω^'-hfib-Trunc : ∀ {i} (n : ℕ) {X : Type i} {x : X} {{_ : has-level (S ⟨ n ⟩) X}}
  → Ω^' (S n) ⊙[ hfiber ([_] {n = ⟨ n ⟩}) [ x ] , (x , idp) ] ≃ Ω^' (S n) ⊙[ X , x ]
Ω^'-hfib-Trunc O {x = x} = Σ-contr-red-cod {{↓-level}} ∘e (=Σ-econv (x , idp) (x , idp)) ⁻¹
Ω^'-hfib-Trunc (S n) {X} {x} {{tX}} = Ω^'-hfib-Trunc n {Ω ⊙[ X , x ]} {idp} ∘e Ω^'-emap (S n) ⊙Ω-hfib-Trunc
