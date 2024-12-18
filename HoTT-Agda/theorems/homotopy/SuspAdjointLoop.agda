{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Suspension
open import lib.types.LoopSpace
open import lib.types.Homogeneous
open import homotopy.PtdAdjoint

module homotopy.SuspAdjointLoop where

module _ {i} where

  SuspFunctor : PtdFunctor i i
  SuspFunctor = record {
    obj = ⊙Susp;
    arr = ⊙Susp-fmap;
    id = ⊙Susp-fmap-idf;
    comp = ⊙Susp-fmap-∘}

  LoopFunctor : PtdFunctor i i
  LoopFunctor = record {
    obj = ⊙Ω;
    arr = ⊙Ω-fmap;
    id = λ _ → ⊙Ω-fmap-idf;
    comp = ⊙Ω-fmap-∘}

  -- counit

  module _ (X : Ptd i) where

    η : de⊙ X → Ω (⊙Susp X)
    η x = σloop X x

    ⊙η : X ⊙→ ⊙Ω (⊙Susp X)
    ⊙η = (η , σloop-pt)

-- induced map of hom types

module _ {i j} (X : Ptd i) (U : Ptd j) where

  into : ⊙Susp X ⊙→ U → X ⊙→ ⊙Ω U
  into r = ⊙Ω-fmap r ⊙∘ ⊙η X

  ap-comp-into-coher-aux : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {x : Susp (de⊙ X)} (v : x == right unit)
    → ! (
        (hmpty-nat-∙'-r H₀ (v ∙ ! v) ∙
          ap (λ p → p ∙ ap g (v ∙ ! v) ∙' ! (H₀ x))
            (! (!-! (H₀ x)) ∙ ! (!-∙ (! (H₀ x)) idp)) ∙
          ap (λ p → ! (! (H₀ x) ∙ idp) ∙ ap g (v ∙ ! v) ∙' p)
            (! (∙-unit-r (! (H₀ x)))) ∙ idp) ∙
        ! (Ω-fmap-β (g , ! (H₀ x) ∙ idp)  (v ∙ ! v))) ∙
      ap (ap f) (!-inv-r v) ∙ idp
      ==
      ap (fst (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))) (!-inv-r v) ∙
      snd (⊙Ω-fmap (g , ! (H₀ x) ∙ idp))
  ap-comp-into-coher-aux {g = g} H₀ idp = lemma (H₀ (right unit))
    where
      lemma : {x : de⊙ U} (u : x == g (right unit))
        → ! (
          ((! (!-inv-r u) ∙
          ap (_∙_ u) (! (∙'-unit-l (! u)))) ∙
          ap (λ p → p ∙ idp ∙' ! u)
            (! (!-! u) ∙ ! (!-∙ (! u) idp)) ∙
          ap (λ p → ! (! u ∙ idp) ∙ idp ∙' p)
            (! (∙-unit-r (! u))) ∙ idp) ∙
          ! (Ω-fmap-β (g , ! u ∙ idp) idp)) ∙ idp
          ==
          snd (⊙Ω-fmap (g , ! u ∙ idp))
      lemma idp = idp

  ap-comp-into-coher : {f g : Susp (de⊙ X) → de⊙ U} (H₀ : f ∼ g)
    {gₚ : g (left unit) == f (left unit)} (H₁ : ! (H₀ (left unit)) ∙ idp == gₚ)
    → ! (
        (hmpty-nat-∙'-r H₀ (glue (pt X) ∙ ! (glue (pt X))) ∙
        ap (λ p → p ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' ! (H₀ (left unit)))
          (! (!-! (H₀ (left unit))) ∙ ! (!-∙ (! (H₀ (left unit))) idp)) ∙
        ap (λ p → ! (! (H₀ (left unit)) ∙ idp) ∙ ap g (glue (pt X) ∙ ! (glue (pt X))) ∙' p)
          (! (∙-unit-r (! (H₀ (left unit))))) ∙
        ∙-∙'-= (ap g (glue (pt X) ∙ ! (glue (pt X)))) H₁) ∙
        ! (Ω-fmap-β (g , gₚ) (glue (pt X) ∙ ! (glue (pt X))))) ∙
      ap (ap f) (!-inv-r (glue (pt X))) ∙ idp
      ==
      ap (Ω-fmap (g , gₚ)) (!-inv-r (glue (pt X))) ∙ snd (⊙Ω-fmap (g , gₚ))
  ap-comp-into-coher H₀ idp = ap-comp-into-coher-aux H₀ (glue (pt X))

  ap-comp-into : {f₁ f₂ : ⊙Susp X ⊙→ U} (H : f₁ ⊙-comp f₂) → into f₁ ⊙-comp into f₂
  fst (ap-comp-into {f₁ = (f , idp)} {f₂} H) x =
    (hmpty-nat-∙'-r (fst H) (glue x ∙ ! (glue (pt X))) ∙
      ap (λ p → p ∙ ap (λ z → fst f₂ z) (glue x ∙ ! (glue (pt X))) ∙' ! (fst H (left unit)))
        (! (!-! (fst H (left unit))) ∙ ! (!-∙ (! (fst H (left unit))) idp)) ∙
      ap (λ p → (! (! (fst H (left unit)) ∙ idp)) ∙ ap (fst f₂) (glue x ∙ ! (glue (pt X))) ∙' p)
        (! (∙-unit-r (! (fst H (left unit))))) ∙
      ∙-∙'-= (ap (fst f₂) (glue x ∙ ! (glue (pt X)))) (snd H)) ∙
    ! (Ω-fmap-β f₂ (glue x ∙ ! (glue (pt X)))) 
  snd (ap-comp-into {f₁ = (f , idp)} {f₂} H) = ap-comp-into-coher (fst H) (snd H)

  {-
     This definition of ap agrees with the standard ap on the id homotopy,
     hence on all homotopies by the SIP.
  -}

  ap-comp-into-id : (f* : ⊙Susp X ⊙→ U) → ap-comp-into (⊙∼-id f*) ⊙→∼ ⊙∼-id (into f*)
  fst (ap-comp-into-id (f , idp)) x = 
    ∙-unit-r (hmpty-nat-∙'-r (λ x₁ → idp) (glue x ∙ ! (glue (pt X))) ∙ idp) ∙
    ∙-unit-r (hmpty-nat-∙'-r (λ x₁ → idp) (glue x ∙ ! (glue (pt X)))) ∙
    hmpty-nat-∙'-r-idp (glue x ∙ ! (glue (pt X)))
  snd (ap-comp-into-id (f , idp)) = =ₛ-in (lemma (glue (pt X)))
    where
      lemma : {x : Susp (de⊙ X)} (v : x == right unit) →
        ap (λ p → ! p ∙ ap (ap f) (!-inv-r v) ∙ idp)
        (∙-unit-r (hmpty-nat-∙'-r (λ x₁ → idp) (v ∙ ! v) ∙ idp) ∙
        ∙-unit-r (hmpty-nat-∙'-r (λ x₁ → idp) (v ∙ ! v)) ∙
        hmpty-nat-∙'-r-idp (v ∙ ! v)) ∙ idp
        ==
        ap-comp-into-coher-aux (λ x → idp) v
      lemma idp = idp
      
{-
  an explicit component-based homotopy witnessing the
  naturality of into in its first argument
-}

module _ {i i' j} {X : Ptd i} {Y : Ptd i'} {U : Ptd j} where 

  module _ (r₀ : Susp (de⊙ Y) → de⊙ U) (h₀ : de⊙ X → de⊙ Y) where

    nat-dom-aux-r : {v : Susp (de⊙ Y)} (τ : left unit == v)
      →
      ! (ap-∙ r₀ τ (! τ) ∙
        (ap-!-inv r₀ τ ∙ ! (cmp-inv-r (glue (pt X)))) ∙
        ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
        (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
        ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
      ap (ap r₀) (!-inv-r τ) ∙ idp
      ==
      ap (ap (r₀ ∘ Susp-fmap h₀)) (!-inv-r (glue (pt X))) ∙ idp
    nat-dom-aux-r idp = ap-!-∘-∙-rid-coher r₀ (Susp-fmap h₀) (glue (pt X))

    nat-dom-aux-l2 : {v : Susp-fmap h₀ (left unit) == Susp-fmap h₀ (right unit)}
      (τ : ap (Susp-fmap h₀) (glue (pt X)) == v)
      →
      ! (ap (_∙_ (ap r₀ v)) (ap (λ p → ap r₀ (! p)) τ)) ∙
      ! (ap (_∙_ (ap r₀ v)) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
        ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ∙
      ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) τ)
      ==
      ap-!-inv r₀ v ∙ ! (cmp-inv-r (glue (pt X)))
    nat-dom-aux-l2 idp = ap-!-∘-rid-coher r₀ (Susp-fmap h₀) (glue (pt X))
    
    nat-dom-aux-l : 
      ! (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
        (ap (λ p → ap r₀ (! p))
        (SuspFmap.merid-β h₀ (pt X)))) ∙
      ! (ap (_∙_ (ap r₀ (glue (h₀ (pt X)))))
        (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
        ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ∙
      ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X))))
        (SuspFmap.merid-β h₀ (pt X)))
      ==
      ap-!-inv r₀ ((merid ∘ h₀) (pt X)) ∙ ! (cmp-inv-r {f = Susp-fmap h₀} {g = r₀} (glue (pt X))) 
    nat-dom-aux-l = nat-dom-aux-l2 (SuspFmap.merid-β h₀ (pt X)) 

  nat-dom : (h : X ⊙→ Y) (r : ⊙Susp Y ⊙→ U)
    → (into Y U) r ⊙∘ h ⊙-comp (into X U) (r ⊙∘ ⊙Susp-fmap h)
  fst (nat-dom (h₀ , idp) (r₀ , idp)) x = ↯ (
    ap-∙ r₀ (glue (h₀ x)) (! (glue (pt Y))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))) ◃∙
    ! (ap (λ p → ap r₀ (glue (h₀ x)) ∙ p) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
      ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))) ◃∙
    ! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ x)) ◃∙
    ! ((ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue x)))) ◃∙
    ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue x) (! (glue (pt X)))) ◃∎
    )
  snd (nat-dom (h₀ , idp) (r₀ , idp)) =
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p) ∙
      ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp)
      (assoc-4-∙
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap (λ p → ap r₀ (! p)) (SuspFmap.merid-β h₀ (pt X)))))
        (! (ap (_∙_ (ap r₀ (glue (h₀ (pt X))))) (ap-∘ r₀ (Susp-fmap h₀) (! (glue (pt X))) ∙
          ap (ap r₀) (ap-! (Susp-fmap h₀) (glue (pt X))))))
        (! (ap (λ p → ap r₀ p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (SuspFmap.merid-β h₀ (pt X))))
        (! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))))
        (! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X)))))) ∙
    ap (λ p → ! (ap-∙ r₀ (glue (h₀ (pt X))) (! (glue (h₀ (pt X)))) ∙ p ∙
      ! (ap (λ p → p ∙ ap (r₀ ∘ Susp-fmap h₀) (! (glue (pt X)))) (ap-∘ r₀ (Susp-fmap h₀) (glue (pt X)))) ∙
      ! (ap-∙ (r₀ ∘ Susp-fmap h₀) (glue (pt X)) (! (glue (pt X))))) ∙
        ap (ap r₀) (!-inv-r (glue (h₀ (pt X)))) ∙ idp) (nat-dom-aux-l r₀ h₀) ∙
    nat-dom-aux-r r₀ h₀ ((glue (h₀ (pt X))))

{- the nat-dom proof makes Susp a 2-coherent left adjoint to Loop -}

-- an ad-hoc data structure for a messy computation required by our 2-coherence proof

module _ {i j k l ℓ} {A : Type i} {B : Type j} {C : Type k} {D : Type l} {E : Type ℓ}
  (m : A → D) (n : B → A) (s : C → A) (r : E → C) where

  record sev_step_red_inp {x₁ x₂ : D} {x₃ x₄ : A} {x₅ x₆ x₇ : B} {x₈ x₁₃ : C}
    {x₉ x₁₀ x₁₁ x₁₂ : E} (q₁ : x₁ == m x₃) (q₂ : x₄ == n x₅) (q₃ : x₅ == x₆)
    (q₄ : x₆ == x₇) {b : B} (q₅ : x₇ == b) (ϕ : n b  == s x₈) (q₆ : x₈ == r x₉)
    (q₇ : x₉ == x₁₀) (q₈ : x₁₀ == x₁₁) (q₉ : x₁₁ == x₁₂) (q₁₀ : r x₁₂ == x₁₃)
    (q₁₁ : s x₁₃ == x₃) (q₁₂ : m x₄ == x₂) (τ : x₁ == x₂)
    {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : D}
    (μ₁ : d₀ == d₁) (μ₂ : d₃ == d₄) (μ₃ : d₀ == d₆)
    (p₁ : d₁ == d₂) (p₂ : d₂ == d₃) (p₃ : d₄ == d₅)
    (p₄ : d₅ == x₁) (p₅ : d₆ == d₇) (p₆ : d₇ == x₂)
    {R₁ : d₃ == m (s (r x₁₁))} {R₂ : d₃ == m (n x₇)} {R₃ : d₀ == m (n x₇)}
    {R₄ : d₀ == m (n x₆)} {R₅ : m (n x₆) == d₇}
      : Type (lmax i (lmax j (lmax k l))) where
    constructor sev_step
    field
      red1 : τ == ((q₁ ∙ ! (ap m (q₂ ∙ ap n (q₃ ∙ q₄ ∙ q₅) ∙ ϕ ∙
        ap s (q₆ ∙ ap r (q₇ ∙ q₈ ∙ q₉) ∙ q₁₀) ∙ q₁₁)) ∙ q₁₂) ∙ idp) ∙ idp
      red2 : μ₂ ∙ p₃ ∙ p₄ ∙ q₁ ∙ ! (ap m (ap s (ap r q₉ ∙ q₁₀) ∙ q₁₁)) == R₁
      red3 : R₁ ∙ ! (ap m (ap n q₅ ∙ ϕ ∙ ap s (q₆ ∙ ap r (q₇ ∙ q₈)))) == R₂
      red4 : μ₁ ∙ p₁ ∙ p₂ ∙ R₂ == R₃
      red5 : R₃ ∙ ! (ap m (ap n q₄)) == R₄
      red6 : ! (ap m (q₂ ∙ ap n q₃)) ∙ q₁₂ ∙ ! p₆ == R₅
      red7 : R₄ ∙ R₅ ∙ ! p₅ ∙ ! μ₃ == idp
  open sev_step_red_inp public

module _ {i j k l ℓ} {A : Type i} {B : Type j} {C : Type k} {D : Type l} {E : Type ℓ}
  {m : A → D} {n : B → A} {s : C → A} {r : E → C} where

  sev_step_reduce : {x₁ x₂ : D} {x₃ x₄ : A} {x₅ x₆ x₇ : B} {x₈ x₁₃ : C}
    {x₉ x₁₀ x₁₁ x₁₂ : E} {q₁ : x₁ == m x₃} {q₂ : x₄ == n x₅} {q₃ : x₅ == x₆}
    {q₄ : x₆ == x₇} {b : B} {q₅ : x₇ == b} {ϕ : n b  == s x₈} {q₆ : x₈ == r x₉}
    {q₇ : x₉ == x₁₀} {q₈ : x₁₀ == x₁₁} {q₉ : x₁₁ == x₁₂} {q₁₀ : r x₁₂ == x₁₃}
    {q₁₁ : s x₁₃ == x₃} {q₁₂ : m x₄ == x₂} {τ : x₁ == x₂}
    {d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : D}
    {μ₁ : d₀ == d₁} {μ₂ : d₃ == d₄} {μ₃ : d₀ == d₆}
    {p₁ : d₁ == d₂} {p₂ : d₂ == d₃} {p₃ : d₄ == d₅}
    {p₄ : d₅ == x₁} {p₅ : d₆ == d₇} {p₆ : d₇ == x₂}
    {R₁ : d₃ == m (s (r x₁₁))} {R₂ : d₃ == m (n x₇)} {R₃ : d₀ == m (n x₇)}
    {R₄ : d₀ == m (n x₆)} {R₅ : m (n x₆) == d₇}
    → sev_step_red_inp m n s r q₁ q₂ q₃ q₄ q₅ ϕ
      q₆ q₇ q₈ q₉ q₁₀ q₁₁ q₁₂ τ μ₁ μ₂ μ₃
      p₁ p₂ p₃ p₄ p₅ p₆ {R₁} {R₂} {R₃} {R₄} {R₅}
    → (μ₁ ∙ p₁ ∙ p₂) ∙ (μ₂ ∙ p₃ ∙ p₄) ∙ τ ∙ ! (μ₃ ∙ p₅ ∙ p₆) == idp
  sev_step_reduce {q₁ = idp} {idp} {idp} {idp} {q₅ = idp}
    {ϕ} {idp} {idp} {idp} {idp} {idp} {idp} {idp} {μ₁ = idp}
    {idp} {idp} {idp} {idp} {idp} {idp} {idp} {p₆}
    (sev_step idp idp idp idp idp idp red7) =
      ap (λ p → p ∙ ! p₆) (∙-unit-r ((! (ap m (ϕ ∙ idp)) ∙ idp) ∙ idp) ∙ ∙-unit-r (! (ap m (ϕ ∙ idp)) ∙ idp)) ∙
      ap (λ p → (! (ap m (ϕ ∙ idp)) ∙ idp) ∙ p) (! (∙-unit-r (! p₆))) ∙
      red7

module _ {i₁ i₂ i₃ i₄} {X : Ptd i₁} {Y : Ptd i₂} {Z : Ptd i₃} {W : Ptd i₄} where 

  -- unfolded version of naturality square for Susp-fmap-∘

  module _ (f₂ : de⊙ Z → de⊙ X) (f₃ : de⊙ W → de⊙ Z) (f₁ : Susp (de⊙ X) → de⊙ Y)
    (x : de⊙ W) where 

    β-free1 : {x : Susp (de⊙ Z)} {ω₁ : left unit == right unit}
      (ω₂ : x == right unit) (ω₃ : left unit == right unit)
      (ω₄ : ap (Susp-fmap f₃) ω₃ == ω₁) →
      ap (f₁ ∘ Susp-fmap f₂) (ω₁ ∙ ! ω₂)
      ==
      ap f₁ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙
        ! (ap (Susp-fmap f₂) ω₂))
    β-free1 {ω₁ = ω₁} ω₂ ω₃ ω₄ =
      ap-∘ f₁ (Susp-fmap f₂) (ω₁ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) ω₁ (! ω₂)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! ω₂))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙
        ap (ap (Susp-fmap f₂)) ω₄))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) ω₂))

    β-red1-aux2 : {w : Susp (de⊙ W)} (ω₆ : left unit == w)
      {𝕗 : ap f₁ (! (SuspMapEq (Susp-fmap (f₂ ∘ f₃))
        (Susp-fmap f₂ ∘ Susp-fmap f₃) idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w)) ∙
      ap f₁ (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w ∙
        ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
      == ap f₁ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))}
      (𝕣 : 𝕗 == ap-!-∙-ap f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆)
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) w)) →
      (! (ap (λ q → q) (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙ idp) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (! ω₆) ∙
      𝕗 ∙ 
      ! (ap (ap f₁) (ap (λ q → q) (ap ! (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
        !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙ idp))
      ==
      ap-∘ f₁ (Susp-fmap f₂) (! (ap (Susp-fmap f₃) ω₆)) ∙
      ap (ap f₁) (ap (λ q → q) (ap-! (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₆)))
    β-red1-aux2 idp idp = idp

    β-red1-aux : {w : Susp (de⊙ W)} (ω₃ ω₆ : left unit == w) →
      ap-∙ (f₁ ∘ Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)
        (! (ap (Susp-fmap f₃) ω₆)) ∙
      (! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆))) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (ω₃ ∙ ! ω₆) ∙
      ! (ap (ap f₁) (ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃))
        (ap ! (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
        !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆)))))
      ==
      ap-∘ f₁ (Susp-fmap f₂) ((ap (Susp-fmap f₃) ω₃) ∙
        ! (ap (Susp-fmap f₃) ω₆)) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃)
        (! (ap (Susp-fmap f₃) ω₆))) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! (ap (Susp-fmap f₃) ω₆)))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙ idp))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₆)))
    β-red1-aux idp ω₆ = β-red1-aux2 ω₆ idp
 
    β-red1 : {ω₁ ω₂ : left unit == right unit}
      (ω₃ : left unit == right unit) (ω₄ : ap (Susp-fmap f₃) ω₃ == ω₁)
      (ω₆ : left unit == right unit) (ω₅ : ap (Susp-fmap f₃) ω₆ == ω₂) → 
      ap-∙ (f₁ ∘ Susp-fmap f₂) ω₁ (! ω₂) ∙
      ! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) ω₁))
        (ap (λ p → ap (f₁ ∘ Susp-fmap f₂) (! p)) ω₅)) ∙
      (! (ap (_∙_ (ap (f₁ ∘ Susp-fmap f₂) ω₁))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) (! ω₆) ∙
        ap (ap (f₁ ∘ Susp-fmap f₂)) (ap-! (Susp-fmap f₃) ω₆))) ∙
      ! (ap (λ p → ap (f₁ ∘ Susp-fmap f₂) p ∙ ap ((f₁ ∘ Susp-fmap f₂) ∘ Susp-fmap f₃)
        (! ω₆)) ω₄) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) (! ω₆))
        (ap-∘ (f₁ ∘ Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ (! ω₆))) ∙
      ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (ω₃ ∙ ! ω₆) ∙
      ! (ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
          (ap ! (! (ap (ap (Susp-fmap f₂)) ω₅) ∙
          ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₆)) ∙
          !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₆) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃
          (! ω₆)))))
      == β-free1 ω₂ ω₃ ω₄
    β-red1 ω₃ idp ω₆ idp = β-red1-aux ω₃ ω₆

    β-free2 : {x₁ x₂ x₃ : Susp (de⊙ Z)} (ω₁ : x₂ == x₃)
      (ω₂ : x₁ == x₃) {ω₇ : Susp-fmap f₂ x₃ == Susp-fmap f₂ x₁}
      (ω₈ : ω₇ == ! (ap (Susp-fmap f₂) ω₂)) → 
      ap (f₁ ∘ Susp-fmap f₂) (ω₁ ∙ ! ω₂)
      ==
      ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ω₇)
    β-free2 ω₁ ω₂ ω₈ =
      ap-∘ f₁ (Susp-fmap f₂) (ω₁ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) ω₁ (! ω₂)) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂) ω₁ ∙ p) (ap-! (Susp-fmap f₂) ω₂)) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂) ω₁ ∙ p) (! ω₈))

    β-red2-aux2 : {x₁ x₂ : Susp (de⊙ Z)} (ω₂ : x₁ == x₂)
      {c : Susp-fmap f₂ x₂ == Susp-fmap f₂ x₁}
      (↑ω₈ : c == ! (ap (Susp-fmap f₂) ω₂)) →
      (ap-∘ f₁ (Susp-fmap f₂) (! ω₂) ∙
        ap (ap f₁) (ap (λ q → q) (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (ap f₁) (ap (λ q → q) ↑ω₈))
      ==
      β-free2 idp ω₂ ↑ω₈
    β-red2-aux2 idp idp = idp

    β-red2-aux : {w : Susp (de⊙ W)} (ω₃ : w == right unit)
      (ω₂ : left unit == right unit)
      (ω₆ : left unit == right unit)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ap (Susp-fmap f₂) ω₂) → 
      (ap-∘ f₁ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃ ∙ ! ω₂) ∙
      ap (ap f₁) (ap-∙ (Susp-fmap f₂) (ap (Susp-fmap f₃) ω₃) (! ω₂)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap f₂) (! ω₂))
        (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃ ∙ idp))) ∙
      ap (ap f₁) (ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙
        ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
        (! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
        ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃))
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))))
      ==
      β-free2 (ap (Susp-fmap f₃) ω₃) ω₂
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))
    β-red2-aux idp ω₂ ω₆ ω₈¹ =
      β-red2-aux2 ω₂ (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ idp))

    β-red2 : (ω₂ : left unit == right unit)
      (ω₃ : left unit == right unit)
      (ω₆ : left unit == right unit)
      {w : left unit == right unit}
      (ω₈² : ap (Susp-fmap f₂) ω₂ == w)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == w)
      {e : Susp-fmap f₃ (left unit) == Susp-fmap f₃ (right unit)}
      (ω₉ : ap (Susp-fmap f₃) ω₃ == e) →
      β-free1 ω₂ ω₃ ω₉ ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
        (! (ap (ap (Susp-fmap f₂)) ω₉) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) ω₃)) ∙
        ap (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) ω₃ ∙ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ ! ω₈²))))
      ==
      β-free2 e ω₂ ((ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! (ω₈¹ ∙ ! ω₈²)))
    β-red2 ω₂ ω₃ ω₆ idp ω₈¹ idp = β-red2-aux ω₃ ω₂ ω₆ ω₈¹

    β-free3 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      {x : Susp (de⊙ W)} (ω₆ : x == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) x == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) → 
      ap f₁ (ω₁₀ ∙ ! ω₁₁)
      ==
      ap f₁ (ap (Susp-fmap f₂) ω₁ ∙
        ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆))
    β-free3 ω₁ ω₆ {ω₁₁} ω₈¹ {ω₁₀} ω₁₂ =
      ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p)) (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)  

    β-red3 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      (ω₂ : left unit == right unit)
      (ω₆ : left unit == right unit)
      {ω₁₁ : left unit == right unit}
      (ω₈² : ap (Susp-fmap f₂) ω₂ == ω₁₁)
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) →
      ap-∙ f₁ ω₁₀ (! ω₁₁) ∙
      ! (ap (_∙_ (ap f₁ ω₁₀))
        (ap (λ p → ap f₁ (! p)) ω₈²)) ∙
      (! (ap (_∙_ (ap f₁ ω₁₀))
         (ap-∘ f₁ (Susp-fmap f₂) (! ω₂) ∙
         ap (ap f₁) (ap-! (Susp-fmap f₂) ω₂))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap f₂) (! ω₂)) ω₁₂) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂) (! ω₂))
        (ap-∘ f₁ (Susp-fmap f₂) ω₁)) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂) ω₁ (! ω₂))) ∙
      β-free2 ω₁ ω₂ (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! (ω₈¹ ∙ ! ω₈²))
      ==
      ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p)) (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)
    β-red3 idp ω₂ ω₆ idp ω₈¹ idp = 
      ap-∘2-ap-! f₁ (Susp-fmap f₂) ω₂
        (ap (ap f₁) (ap (λ p → p) (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! (ω₈¹ ∙ idp))))) ∙
      ap3-!-ap-!-rid (Susp-fmap (f₂ ∘ f₃)) f₁ ω₆ ω₈¹

    β-red4 : {y : Susp (de⊙ Z)} (ω₁ : y == right unit)
      {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) w == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁)
      {ω₁₀ : Susp-fmap f₂ y == right unit}
      (ω₁₂ : ap (Susp-fmap f₂) ω₁ == ω₁₀) → 
      (ap (λ p → ap f₁ (p ∙ ! ω₁₁)) (! ω₁₂) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ ! p))
        (! ω₈¹) ∙
      ap (λ p → ap f₁ (ap (Susp-fmap f₂) ω₁ ∙ p))
        (!-ap (Susp-fmap (f₂ ∘ f₃)) ω₆)) ∙
      ! (ap (ap f₁) (ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃))
        (! ω₆)) (! ω₁₂)))
      ==
      ap (λ p → ap f₁ (ω₁₀ ∙ p))
        (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙ ap ! ω₈¹))
    β-red4 idp idp idp idp = idp

    β-red5 : {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      (ω₃ : left unit == right unit)
      {ω₁₀ : left unit == right unit}
      (ω₁₃ : ap (Susp-fmap (f₂ ∘ f₃)) ω₃ == ω₁₀) → 
      ! (ap (ap f₁) (ap-∙ (Susp-fmap (f₂ ∘ f₃)) ω₃
        (! ω₆) ∙ ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃))
        (! ω₆)) ω₁₃)) ∙
      ! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (ω₃ ∙ ! ω₆))) ∙
      ! (! (ap (_∙_ (ap f₁ ω₁₀))
          (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (! ω₆) ∙
          ap (ap f₁) (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆))) ∙
        ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃))
          (! ω₆)) ω₁₃) ∙
        ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (! ω₆))
          (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) ω₃)) ∙
        ! (ap-∙ (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) ω₃ (! ω₆)))
      ==
      ap-∙ f₁ ω₁₀ (ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆)) ∙
      ap (λ p → ap f₁ ω₁₀ ∙ ap f₁ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆)
    β-red5 idp ω₃ idp = ap-∘2-ap-∙ f₁ (Susp-fmap (f₂ ∘ f₃)) ω₃

    β-red6 : {x : Susp (de⊙ X)} (ω₁₀ : x == right unit)
      {w : Susp (de⊙ W)} (ω₆ : w == right unit)
      {ω₁₁ : Susp-fmap (f₂ ∘ f₃) w == right unit}
      (ω₈¹ : ap (Susp-fmap (f₂ ∘ f₃)) ω₆ == ω₁₁) →
      ap (λ p → ap f₁ (ω₁₀ ∙ p))
        (! (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆ ∙
        ap ! ω₈¹)) ∙
      (ap-∙ f₁ ω₁₀ (ap (Susp-fmap (f₂ ∘ f₃)) (! ω₆)) ∙
      ap (λ p → ap f₁ ω₁₀ ∙ ap f₁ p)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) ω₆)) ∙
      ! (! (ap (_∙_ (ap f₁ ω₁₀))
        (ap (λ p → ap f₁ (! p)) ω₈¹))) ∙
      ! (ap-∙ f₁ ω₁₀ (! ω₁₁))
      == idp
    β-red6 idp idp idp = idp

    Susp-fmap-∘-sq-rw : 
      (hmpty-nat-∙'-r (λ z → ap f₁ (! (Susp-fmap-∘-∼ f₂ f₃ z)))
        (merid x ∙ ! (merid (pt W))) ∙ idp) ∙ idp
        ==
      ((ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (merid x ∙ ! (merid (pt W))) ∙
      ! (ap (ap f₁) (
        ap-∙ (Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W))) ∙
        ap (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
          (SuspFmap.merid-β (f₂ ∘ f₃) x ∙ ! (SuspFmap.merid-β f₂ (f₃ x)) ∙
          ! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ x)) ∙
          ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid x))) ∙
        ap (_∙_ (ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)))
          (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W)) ∙
          ap ! (SuspFmap.merid-β (f₂ ∘ f₃) (pt W) ∙
            ! (SuspFmap.merid-β f₂ (f₃ (pt W))) ∙
            ! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ (pt W))) ∙
            ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid (pt W)))) ∙
          !-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid (pt W))) ∙
        ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)
          (! (merid (pt W))))))) ∙
      ! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (merid x ∙ ! (merid (pt W)))))) ∙
      idp) ∙ idp
    Susp-fmap-∘-sq-rw = ap (λ p → (p ∙ idp) ∙ idp) (SuspMapEq-β-∙-ap! (Susp-fmap (f₂ ∘ f₃))
      (Susp-fmap f₂ ∘ Susp-fmap f₃) idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x)) f₁ x (pt W))

    -- proof of 2-coherence

    two_coher_Susp-∼ : sev_step_red_inp (ap f₁)
      (λ p → p ∙ ap (Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
      (λ p → ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x) ∙ p) !
      (ap-∘-long f₁ (Susp-fmap f₂ ∘ Susp-fmap f₃) (Susp-fmap (f₂ ∘ f₃))
        (SuspMapEq (Susp-fmap (f₂ ∘ f₃)) (Susp-fmap f₂ ∘ Susp-fmap f₃)
        idp idp (λ x → ↯ (Susp-fmap-∘ f₂ f₃ x))) (merid x ∙ ! (merid (pt W))))
      (ap-∙ (Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W))))
      (SuspFmap.merid-β (f₂ ∘ f₃) x)
      (! (SuspFmap.merid-β f₂ (f₃ x)))
      (! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ x)) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid x)))
      idp (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W)))
      (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
      (! (SuspFmap.merid-β f₂ (f₃ (pt W))))
      (! (ap (ap (Susp-fmap f₂)) (SuspFmap.merid-β f₃ (pt W))) ∙
        ! (ap-∘ (Susp-fmap f₂) (Susp-fmap f₃) (merid (pt W))))
      (!-ap (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid (pt W)))
      (ap (λ p → p) (! (ap-∙ (Susp-fmap f₂ ∘ Susp-fmap f₃) (merid x)
        (! (merid (pt W))))))
      (! (ap (λ q → q) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (merid x ∙ ! (merid (pt W))))))
      ((hmpty-nat-∙'-r (λ z → ap f₁ (! (Susp-fmap-∘-∼ f₂ f₃ z)))
        (merid x ∙ ! (merid (pt W))) ∙ idp) ∙ idp)
      (ap-∙ f₁ (merid (f₂ (f₃ x))) (! (merid (f₂ (f₃ (pt W))))))
      (ap-∙ (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x)) (! (merid (f₃ (pt W)))))
      (ap-∙ f₁ (merid (f₂ (f₃ x))) (! (merid (f₂ (f₃ (pt W))))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap (λ p → ap f₁ (! p))
        (SuspFmap.merid-β f₂ (f₃ (pt W))))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x)))))
        (ap-∘ f₁ (Susp-fmap f₂) (! (merid (f₃ (pt W)))) ∙
        ap (ap f₁) (ap-! (Susp-fmap f₂) (merid (f₃ (pt W)))))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (merid (f₃ (pt W)))))
        (SuspFmap.merid-β f₂ (f₃ x))) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap f₂) (! (merid (f₃ (pt W)))))
        (ap-∘ f₁ (Susp-fmap f₂) (merid (f₃ x)))) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap f₂) (merid (f₃ x)) (! (merid (f₃ (pt W))))))
      (! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x))))
        (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) (! p))
        (SuspFmap.merid-β f₃ (pt W)))))
      (! (ap (_∙_ (ap (f₁ ∘ (Susp-fmap f₂)) (merid (f₃ x))))
        (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃) (! (merid (pt W))) ∙
        ap (ap (f₁ ∘ (Susp-fmap f₂))) (ap-! (Susp-fmap f₃) (merid (pt W))))) ∙
      ! (ap (λ p → ap (f₁ ∘ (Susp-fmap f₂)) p ∙
        ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃) (! (merid (pt W))))
        (SuspFmap.merid-β f₃ x)) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
        (! (merid (pt W)))) (ap-∘ (f₁ ∘ (Susp-fmap f₂)) (Susp-fmap f₃)
        (merid x))) ∙
      ! (ap-∙ (f₁ ∘ (Susp-fmap f₂) ∘ Susp-fmap f₃)
        (merid x) (! (merid (pt W)))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap (λ p → ap f₁ (! p))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W)))))
      (! (ap (_∙_ (ap f₁ (merid (f₂ (f₃ x))))) (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃))
        (! (merid (pt W))) ∙ ap (ap f₁)
        (ap-! (Susp-fmap (f₂ ∘ f₃)) (merid (pt W))))) ∙
      ! (ap (λ p → ap f₁ p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃))
        (! (merid (pt W)))) (SuspFmap.merid-β (f₂ ∘ f₃) x)) ∙
      ! (ap (λ p → p ∙ ap (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (! (merid (pt W))))
        (ap-∘ f₁ (Susp-fmap (f₂ ∘ f₃)) (merid x))) ∙
      ! (ap-∙ (f₁ ∘ Susp-fmap (f₂ ∘ f₃)) (merid x) (! (merid (pt W)))))
    red1 two_coher_Susp-∼ = Susp-fmap-∘-sq-rw
    red2 two_coher_Susp-∼ = 
      β-red1 (merid x) (SuspFmap.merid-β f₃ x) (merid (pt W))
        (SuspFmap.merid-β f₃ (pt W))
    red3 two_coher_Susp-∼ = 
      β-red2 (merid (f₃ (pt W))) (merid x) (merid (pt W))
        (SuspFmap.merid-β f₂ (f₃ (pt W)))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
        (SuspFmap.merid-β f₃ x)
    red4 two_coher_Susp-∼ =
      β-red3 (merid (f₃ x)) (merid (f₃ (pt W))) (merid (pt W))
      (SuspFmap.merid-β f₂ (f₃ (pt W))) (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
      (SuspFmap.merid-β f₂ (f₃ x))
    red5 two_coher_Susp-∼ =
      β-red4 (merid (f₃ x)) (merid (pt W))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))
        (SuspFmap.merid-β f₂ (f₃ x))
    red6 two_coher_Susp-∼ =
      β-red5 (merid (pt W)) (merid x) (SuspFmap.merid-β (f₂ ∘ f₃) x) 
    red7 two_coher_Susp-∼ =
      β-red6 (merid (f₂ (f₃ x))) (merid (pt W))
        (SuspFmap.merid-β (f₂ ∘ f₃) (pt W))

  {-
    It suffices to prove that the underlying homotopies are equal
    because loop spaces are coherently homogeneous.
  -}
  
  two_coher_Susp : (h₁ : ⊙Susp X ⊙→ Y) (h₂ : Z ⊙→ X) (h₃ : W ⊙→ Z) →
    !-⊙∼ (⊙∘-assoc-comp (into X Y h₁) h₂ h₃) ∙⊙∼
    ⊙∘-pre h₃ (nat-dom h₂ h₁) ∙⊙∼
    nat-dom h₃ (h₁ ⊙∘ ⊙Susp-fmap h₂) ∙⊙∼
    ap-comp-into W Y (⊙∘-assoc-comp h₁ (⊙Susp-fmap h₂) (⊙Susp-fmap h₃) ∙⊙∼
      ⊙∘-post h₁ (!-⊙∼ (Susp-fmap-∘-∼ (fst h₂) (fst h₃) , idp))) ∙⊙∼
    !-⊙∼ (nat-dom (h₂ ⊙∘ h₃) h₁)
      ⊙→∼
    ⊙∼-id ((into X Y h₁) ⊙∘ h₂ ⊙∘ h₃)
  two_coher_Susp (f₁ , idp) (f₂ , idp) (f₃ , idp) =
    ∼⊙Ωhomog∼ λ x → sev_step_reduce (two_coher_Susp-∼ f₂ f₃ f₁ x)
