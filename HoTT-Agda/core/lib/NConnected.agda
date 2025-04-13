{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NType2
open import lib.Equivalence2
open import lib.types.Unit
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.TLevel
open import lib.types.Truncation

module lib.NConnected where

is-connected : ∀ {i} → ℕ₋₂ → Type i → Type i
is-connected n A = is-contr (Trunc n A)

has-conn-fibers : ∀ {i j} {A : Type i} {B : Type j} → ℕ₋₂ → (A → B) → Type (lmax i j)
has-conn-fibers {A = A} {B = B} n f =
  Π B (λ b → is-connected n (hfiber f b))

{- all types are -2-connected -}
-2-conn : ∀ {i} (A : Type i) → is-connected -2 A
-2-conn A = Trunc-level

{- all inhabited types are -1-connected -}
inhab-conn : ∀ {i} {A : Type i} (a : A) → is-connected -1 A
inhab-conn a = has-level-in ([ a ] , prop-has-all-paths [ a ])

{- connectedness is a prop -}
is-connected-is-prop : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → is-prop (is-connected n A)
is-connected-is-prop = is-contr-is-prop

-- relation between 0-connectedness and path connectedness
abstract
  conn-path-conn : ∀ {i} {A : Type i} {{_ : is-connected 0 A}}
    (x y : A) → Trunc -1 (x == y)
  conn-path-conn {A = A} x y = –> (=ₜ-equiv [ x ] [ y ]) (contr-has-all-paths [ x ] [ y ])

  path-conn-conn : ∀ {i} {A : Type i} (b : Trunc 0 A)
    → ((x y : A) → Trunc -1 (x == y)) → is-connected 0 A
  path-conn-conn {A = A} b ps = inhab-prop-is-contr b
    {{all-paths-is-prop (Trunc-elim (λ r₁ → Trunc-elim (λ r₂ → <– (=ₜ-equiv [ r₁ ] [ r₂ ]) (ps r₁ r₂))))}}

{- "induction principle" for n-connected maps (where codomain is n-type) -}
abstract
  pre∘-conn-is-equiv : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂}
    → {h : A → B} → has-conn-fibers n h
    → (∀ {k} (P : B → n -Type k) → is-equiv (λ (s : Π B (fst ∘ P)) → s ∘ h))
  pre∘-conn-is-equiv {A = A} {B = B} {n = n} {h = h} c P = is-eq f g f-g g-f
    where f : Π B (fst ∘ P) → Π A (fst ∘ P ∘ h)
          f k a = k (h a)

          helper : Π A (fst ∘ P ∘ h)
            → (b : B) → Trunc n (Σ A (λ a → h a == b)) → (fst (P b))
          helper t b r =
            Trunc-rec {{snd (P b)}}
              (λ x → transport (λ y → fst (P y)) (snd x) (t (fst x)))
              r

          g : Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
          g t b = helper t b (contr-center (c b))

          f-g : ∀ t → f (g t) == t
          f-g t = λ= $ λ a → transport
            (λ r →  Trunc-rec {{snd (P (h a))}} _ r == t a)
            (! (contr-path(c (h a)) [ (a , idp) ]))
            idp

          g-f : ∀ k → g (f k) == k
          g-f k = λ= $ λ (b : B) →
            Trunc-elim {{λ {r} → =-preserves-level {x = helper (k ∘ h) b r} (snd (P b))}}
                       (λ x → lemma (fst x) b (snd x)) (contr-center (c b))
            where
            lemma : ∀ xl → ∀ b → (p : h xl == b) →
              helper (k ∘ h) b [ (xl , p) ] == k b
            lemma xl ._ idp = idp

conn-extend : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  → {h : A → B} → has-conn-fibers n h
  → (P : B → n -Type k)
  → Π A (fst ∘ P ∘ h) → Π B (fst ∘ P)
conn-extend c P f = is-equiv.g (pre∘-conn-is-equiv c P) f

conn-out = conn-extend

conn-extend-β : ∀ {i j k} {A : Type i} {B : Type j} {n : ℕ₋₂}
  {h : A → B} (c : has-conn-fibers n h)
  (P : B → n -Type k) (f : Π A (fst ∘ P ∘ h))
  → ∀ a → (conn-extend c P f (h a)) == f a
conn-extend-β c P f = app= (is-equiv.f-g (pre∘-conn-is-equiv c P) f)


{- generalized "almost induction principle" for maps into ≥n-types
   TODO: rearrange this to use ≤T?                                 -}
conn-extend-general : ∀ {i j} {A : Type i} {B : Type j} {n k : ℕ₋₂}
  → {f : A → B} → has-conn-fibers n f
  → ∀ {l} (P : B → (k +2+ n) -Type l)
  → ∀ t → has-level k (Σ (Π B (fst ∘ P)) (λ s → (s ∘ f) == t))
conn-extend-general {k = ⟨-2⟩} c P t =
  equiv-is-contr-map (pre∘-conn-is-equiv c P) t
conn-extend-general {B = B} {n = n} {k = S k'} {f = f} c P t = has-level-in
  λ {(g , p) (h , q) →
    equiv-preserves-level (e g h p q)
      {{conn-extend-general {k = k'} c (Q g h) (app= (p ∙ ! q))}} }
  where
    Q : (g h : Π B (fst ∘ P)) → B → (k' +2+ n) -Type _
    Q g h b = ((g b == h b) , has-level-apply (snd (P b)) _ _)

    app=-pre∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : B → Type k}
      (f : A → B) {g h : Π B C} (p : g == h)
      → app= (ap (λ k → k ∘ f) p) == app= p ∘ f
    app=-pre∘ f idp = idp

    move-right-on-right-econv : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : x == z) (r : y == z)
      → (p == q ∙ ! r) ≃ (p ∙ r == q)
    move-right-on-right-econv {x = x} p idp idp =
      (_ , pre∙-is-equiv (∙-unit-r p))

    lemma : ∀ g h p q → (H : g ∼ h)
      → ((H ∘ f) == app= (p ∙ ! q))
         ≃ (ap (λ v → v ∘ f) (λ= H) ∙ q == p)
    lemma g h p q H =
      move-right-on-right-econv (ap (λ v → v ∘ f) (λ= H)) p q
      ∘e transport (λ w → (w == app= (p ∙ ! q))
                      ≃ (ap (λ v → v ∘ f) (λ= H) == p ∙ ! q))
                   (app=-pre∘ f (λ= H) ∙ ap (λ k → k ∘ f) (λ= $ app=-β H))
                   (ap-equiv app=-equiv _ _ ⁻¹)

    e : ∀ g h p q  →
      (Σ (g ∼ h) (λ r → (r ∘ f) == app= (p ∙ ! q)))
      ≃ ((g , p) == (h , q))
    e g h p q =
      ((=Σ-econv _ _ ∘e Σ-emap-r (λ u → ↓-app=cst-econv ∘e !-equiv))
      ∘e (Σ-emap-l _ λ=-equiv)) ∘e Σ-emap-r (lemma g h p q)


conn-in : ∀ {i j} {A : Type i} {B : Type j} {n : ℕ₋₂} {h : A → B}
  → (∀ (P : B → n -Type (lmax i j))
     → Σ (Π A (fst ∘ P ∘ h) → Π B (fst ∘ P))
         (λ u → ∀ (t : Π A (fst ∘ P ∘ h)) → u t ∘ h ∼ t))
  → has-conn-fibers n h
conn-in {A = A} {B = B} {h = h} sec b =
  let s = sec (λ b → (Trunc _ (hfiber h b) , Trunc-level))
  in has-level-in (fst s (λ a → [ a , idp ]) b ,
      Trunc-elim (λ k → transport
                   (λ v → fst s (λ a → [ a , idp ]) (fst v) == [ fst k , snd v ])
                   (contr-path (pathfrom-is-contr (h (fst k))) (b , snd k))
                   (snd s (λ a → [ a , idp ]) (fst k))))

abstract
  pointed-conn-in : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    → has-conn-fibers {A = ⊤} n (cst a₀) → is-connected (S n) A
  pointed-conn-in {n = n} A a₀ c = has-level-in
    ([ a₀ ] ,
     Trunc-elim
       (λ a → Trunc-rec
             (λ x → ap [_] (snd x)) (contr-center $ c a)))

abstract
  pointed-conn-out : ∀ {i} {n : ℕ₋₂} (A : Type i) (a₀ : A)
    {{_ : is-connected (S n) A}} → has-conn-fibers {A = ⊤} n (cst a₀)
  pointed-conn-out {n = n} A a₀ {{c}} a = has-level-in
    (point ,
     λ y → ! (cancel point)
           ∙ (ap out $ contr-has-all-paths (into point) (into y))
           ∙ cancel y)
    where
      into-aux : Trunc n (Σ ⊤ (λ _ → a₀ == a)) → Trunc n (a₀ == a)
      into-aux = Trunc-fmap snd

      into : Trunc n (Σ ⊤ (λ _ → a₀ == a))
        → [_] {n = S n} a₀ == [ a ]
      into = <– (=ₜ-equiv [ a₀ ] [ a ]) ∘ into-aux

      out-aux : Trunc n (a₀ == a) → Trunc n (Σ ⊤ (λ _ → a₀ == a))
      out-aux = Trunc-fmap (λ p → (tt , p))

      out : [_] {n = S n} a₀ == [ a ] → Trunc n (Σ ⊤ (λ _ → a₀ == a))
      out = out-aux ∘ –> (=ₜ-equiv [ a₀ ] [ a ])

      cancel : (x : Trunc n (Σ ⊤ (λ _ → a₀ == a))) → out (into x) == x
      cancel x =
        out (into x)
          =⟨ ap out-aux (<–-inv-r (=ₜ-equiv [ a₀ ] [ a ]) (into-aux x)) ⟩
        out-aux (into-aux x)
          =⟨ Trunc-fmap-∘ _ _ x ⟩
        Trunc-fmap (λ q → (tt , (snd q))) x
          =⟨ Trunc-elim {P = λ x → Trunc-fmap (λ q → (tt , snd q)) x == x}
               (λ _ → idp) x ⟩
        x =∎

      point : Trunc n (Σ ⊤ (λ _ → a₀ == a))
      point = out $ contr-has-all-paths [ a₀ ] [ a ]

prop-over-connected :  ∀ {i j} {A : Type i} {a : A} {{p : is-connected 0 A}}
  → (P : A → hProp j)
  → fst (P a) → Π A (fst ∘ P)
prop-over-connected P x = conn-extend (pointed-conn-out _ _) P (λ _ → x)

module _ {i j} {A : Type i} (a : A) {n : ℕ₋₂} {{_ : is-connected (S n) A}} (P : A → Type j)
  {{tr : {x : A} → has-level n (P x)}} where

  conn-extend-ptd : P a → (x : A) → P x
  conn-extend-ptd b = conn-out (pointed-conn-out A a) (λ x → P x , tr) (λ _ → b)

  conn-extend-ptd-β : (b : P a) → conn-extend-ptd b a == b 
  conn-extend-ptd-β b = conn-extend-β (pointed-conn-out A a) (λ x → P x , tr) (λ _ → b) tt

  
