{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Unit
open import lib.types.Paths

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  susp-span : Span
  susp-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Susp : Type i
  Susp = Pushout susp-span

  -- [north'] and [south'] explictly ask for [A]

  north' : Susp
  north' = left tt

  south' : Susp
  south' = right tt

module _ {i} {A : Type i} where

  north : Susp A
  north = north' A

  south : Susp A
  south = south' A

  merid : A → north == south
  merid x = glue x

  module SuspElim {j} {P : Susp A → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ]) where
    open module P = PushoutElim (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspElim public using () renaming (f to Susp-elim)

  module SuspRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    open module P = PushoutRec {d = susp-span A} (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspRec public using () renaming (f to Susp-rec)

susp-⊙span : ∀ {i} → Ptd i → ⊙Span
susp-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp ⊙[ A , _ ] = ⊙[ Susp A , north ]

σloop : ∀ {i} (X : Ptd i) → de⊙ X → north' (de⊙ X) == north' (de⊙ X)
σloop ⊙[ _ , x₀ ] x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (pt X) == idp
σloop-pt {X = ⊙[ _ , x₀ ]} = !-inv-r (merid x₀)

⊙σloop : ∀ {i} (X : Ptd i) → X ⊙→ ⊙[ north' (de⊙ X) == north' (de⊙ X) , idp ]
⊙σloop X = σloop X , σloop-pt

module _ {i j} {A : Type i} {B : Type j} (f g : Susp A → B)
  (n : f north == g north) (s : f south == g south)
  (c : (a : A) → ap f (merid a) == n ∙ ap g (merid a) ∙' ! s) where

  SuspMapEq : f ∼ g
  SuspMapEq = Susp-elim n s λ a → from-hmtpy-nat f g (merid a) (c a)

  SuspMapEq-β : (a : A) → hmtpy-nat-∙'-r SuspMapEq (merid a) == c a
  SuspMapEq-β a =
    apd-to-hnat f g SuspMapEq (merid a) (c a)
      (SuspElim.merid-β n s (λ z → from-hmtpy-nat f g (merid z) (c z)) a)

  SuspMapEq-!-β : (a : A) →
   hmtpy-nat-∙'-r SuspMapEq (! (merid a))
   ==
   ap-! f (merid a) ∙ ap ! (c a) ∙ !-∙-ap-∙'-! g n (merid a) s
  SuspMapEq-!-β a = apd-to-hnat-! f g SuspMapEq (merid a) (SuspMapEq-β a)

  SuspMapEq-β-∙ : (a b : A) →
    hmtpy-nat-∙'-r SuspMapEq (merid a ∙ ! (merid b))
    ==
    ap-∙ f (merid a) (! (merid b)) ∙
    ap (λ p → p ∙ ap f (! (merid b))) (c a) ∙
    ap (_∙_ (SuspMapEq north ∙ ap g (merid a) ∙' ! (SuspMapEq south)))
      (ap-! f (merid b) ∙ ap ! (c b) ∙ !-∙-ap-∙'-! g n (merid b) s) ∙
    assoc-tri-!-mid (SuspMapEq north) (ap g (merid a)) (SuspMapEq south)
      (ap g (! (merid b))) (! (SuspMapEq north)) ∙
    ap (λ p → SuspMapEq north ∙ p ∙' ! (SuspMapEq north))
      (! (ap-∙ g (merid a) (! (merid b))))
  SuspMapEq-β-∙ a b =
    apd-to-hnat-∙ f g SuspMapEq (merid a) (! (merid b)) (SuspMapEq-β a) (SuspMapEq-!-β b)

  SuspMapEq-β-∙-ap! : ∀ {l} {C : Type l} (k : B → C) (a b : A) →
    hmtpy-nat-∙'-r (λ z → ap k (! (SuspMapEq z))) (merid a ∙ ! (merid b))
    ==
    ap-∘-long k g f SuspMapEq (merid a ∙ ! (merid b)) ∙
    ! (ap (λ q → ap k (! (SuspMapEq north)) ∙ ap k q ∙' ! (ap k (! (SuspMapEq north))))
      (ap-∙ f (merid a) (! (merid b)) ∙ ap (λ p → p ∙ ap f (! (merid b))) (c a) ∙
      ap (_∙_ (SuspMapEq north ∙ ap g (merid a) ∙' ! (SuspMapEq south)))
      (ap-! f (merid b) ∙ ap ! (c b) ∙ !-∙-ap-∙'-! g n (merid b) s) ∙
      assoc-tri-!-mid (SuspMapEq north) (ap g (merid a))
      (SuspMapEq south) (ap g (! (merid b))) (! (SuspMapEq north)) ∙
      ap (λ p → SuspMapEq north ∙ p ∙' ! (SuspMapEq north))
      (! (ap-∙ g (merid a) (! (merid b)))))) ∙
    ! (ap (λ q → ap k (! (SuspMapEq north)) ∙ q ∙' ! (ap k (! (SuspMapEq north))))
      (ap-∘ k f (merid a ∙ ! (merid b))))
  SuspMapEq-β-∙-ap! k a b = apd-to-hnat-ap! f g SuspMapEq k (merid a ∙ ! (merid b)) (SuspMapEq-β-∙ a b)

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspRec north south (merid ∘ f)

  Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Susp A → Susp B)
  Susp-fmap = SuspFmap.f

  ⊙Susp-fmap : {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙Susp X ⊙→ ⊙Susp Y
  ⊙Susp-fmap (f , fpt) = (Susp-fmap f , idp)

module _ {i} where

  Susp-fmap-idf : (A : Type i) → ∀ a → Susp-fmap (idf A) a == a
  Susp-fmap-idf A = Susp-elim idp idp $ λ a →
    ↓-='-in' (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙Susp-fmap-idf : (X : Ptd i)
    → ⊙Susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙Susp-fmap-idf X = ⊙λ=' (Susp-fmap-idf (de⊙ X)) idp

module _ {i j k} where

  Susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B) (a : A)
    → ap (Susp-fmap (g ∘ f)) (merid a) =-= ap (Susp-fmap g ∘ Susp-fmap f) (merid a)
  Susp-fmap-∘ g f =
    λ a → 
      ap (Susp-fmap (g ∘ f)) (merid a)
        =⟪ SuspFmap.merid-β (g ∘ f) a ⟫
      merid (g (f a))
        =⟪ ! (SuspFmap.merid-β g (f a)) ⟫
      ap (Susp-fmap g) (merid (f a))
        =⟪ ! (ap (ap (Susp-fmap g)) (SuspFmap.merid-β f a)) ⟫
      ap (Susp-fmap g) (ap (Susp-fmap f) (merid a))
        =⟪ ! (ap-∘ (Susp-fmap g) (Susp-fmap f) (merid a)) ⟫
      ap (Susp-fmap g ∘ Susp-fmap f) (merid a) ∎∎ 

module _ {i j k} {X : Type i} {Y : Type j} {Z : Type k} (g : Y → Z) (f : X → Y) where

  Susp-fmap-∘-∼ =
    SuspMapEq (Susp-fmap (g ∘ f)) (Susp-fmap g ∘ Susp-fmap f) idp idp
      (λ a → ↯ (Susp-fmap-∘ g f a))

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} (g : Y ⊙→ Z) (f : X ⊙→ Y) where

  ⊙Susp-fmap-∘ : ⊙Susp-fmap (g ⊙∘ f) == ⊙Susp-fmap g ⊙∘ ⊙Susp-fmap f
  ⊙Susp-fmap-∘ = ⊙λ=' (Susp-fmap-∘-∼ (fst g) (fst f)) idp

{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtractGlue = PushoutRec {d = s} {D = Susp (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  extract-glue = ExtractGlue.f

  module _ {x₀ : Span.A s} where

    ⊙extract-glue : ⊙[ Pushout s , left x₀ ] ⊙→ ⊙[ Susp (Span.C s) , north ]
    ⊙extract-glue = extract-glue , idp
