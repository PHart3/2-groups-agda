{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.FTID
open import lib.types.Sigma
open import lib.wild-cats.WildCat using (equiv-wc)
open import Bicategory
open import Bicat-coher
open import Bicat-wild

module AdjEq {i j} {B₀ : Type i} where

open BicatStr {{...}}

-- adjoint equivalence structure on a 1-cell of a bicategory

record Adjequiv {{_ : BicatStr j B₀}} {a b : B₀} (f : hom a b) : Type (lmax i j) where
  constructor Adj-eqv
  field
    inv : hom b a
    eta : id₁ a == inv ◻ f
    eps : id₁ b == f ◻ inv
    coher-map : ρ f ∙ ap (λ m → f ◻ m) eta ∙ α f inv f == lamb f ∙ ap (λ m → m ◻ f) eps
    coher-inv : ρ inv ∙ ap (λ m → inv ◻ m) eps ∙ α inv f inv == lamb inv ∙ ap (λ m → m ◻ inv) eta

  coher-map-◃ : ρ f ◃∙ ap (λ m → f ◻ m) eta ◃∙ α f inv f ◃∎ =ₛ lamb f ◃∙ ap (λ m → m ◻ f) eps ◃∎
  coher-map-◃ = =ₛ-in coher-map

  coher-map-rot : ap (λ m → f ◻ m) eta ◃∎ =ₛ ! (ρ f) ◃∙ lamb f ◃∙ ap (λ m → m ◻ f) eps ◃∙ ! (α f inv f) ◃∎
  coher-map-rot = pre-rotate-in (post-rotate-in coher-map-◃)

  coher-inv-◃ : ρ inv ◃∙ ap (λ m → inv ◻ m) eps ◃∙ α inv f inv ◃∎ =ₛ lamb inv ◃∙ ap (λ m → m ◻ inv) eta ◃∎
  coher-inv-◃ = =ₛ-in coher-inv

  coher-inv-rot : ρ inv ◃∙ ap (λ m → inv ◻ m) eps ◃∙ α inv f inv ◃∙ ! (ap (λ m → m ◻ inv) eta) ◃∎ =ₛ lamb inv ◃∎
  coher-inv-rot = post-rotate'-in coher-inv-◃

open Adjequiv

-- induced internal equivalence in underlying wild category
aeqv-to-weqv : {{ξB : BicatStr j B₀}} {a b : B₀} {f : hom {{ξB}} a b} → Adjequiv f → equiv-wc (bc-to-wc (B₀ , ξB)) f
fst (aeqv-to-weqv ae) = inv ae
fst (snd (aeqv-to-weqv ae)) = eta ae
snd (snd (aeqv-to-weqv ae)) = eps ae

Adjequiv-whisk-r-≃ : {{_ : BicatStr j B₀}} {a b c : B₀} {f : hom a b} → Adjequiv f → (hom b c) ≃ (hom a c) 
Adjequiv-whisk-r-≃ {f = f} ae = equiv (λ m → m ◻ f) (λ m → m ◻ inv ae)
  (λ m → ! (α m (inv ae) f) ∙ ! (ap (λ k → m ◻ k) (eta ae)) ∙ ! (ρ m))
  λ m → ! (α m f (inv ae)) ∙ ! (ap (λ k → m ◻ k) (eps ae)) ∙ ! (ρ m)

AdjEquiv : (ξB : BicatStr j B₀) (a b : B₀) → Type (lmax i j)
AdjEquiv ξB a b = Σ (hom {{ξB}} a b) (λ f → Adjequiv {{ξB}} f)

module _ {{ξB : BicatStr j B₀}} where

  AdjEq-rev :  {a b : B₀} → AdjEquiv ξB a b → AdjEquiv ξB b a
  fst (AdjEq-rev (f , ae)) = inv ae
  inv (snd (AdjEq-rev (f , ae))) = f
  eta (snd (AdjEq-rev (f , ae))) = eps ae
  eps (snd (AdjEq-rev (f , ae))) = eta ae
  coher-map (snd (AdjEq-rev (f , ae))) = coher-inv ae
  coher-inv (snd (AdjEq-rev (f , ae))) = coher-map ae

  AdjEq-rev-≃ :  {a b : B₀} → AdjEquiv ξB a b ≃ AdjEquiv ξB b a
  AdjEq-rev-≃ = equiv AdjEq-rev AdjEq-rev (λ _ → idp) λ _ → idp

module ae-unique {{_ : BicatStr j B₀}} {a b : B₀} {f : hom a b} where

  -- extensional equality of adjoint equivalence structures
  infix 30 _Adjeq≃_
  _Adjeq≃_ : Adjequiv f → Adjequiv f → Type j
  α₁ Adjeq≃ α₂ = [ e-inv ∈ inv α₁ == inv α₂ ] ×
    ((eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂) × (eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps α₂))

  Adjeq≃-idf : (α₁ : Adjequiv f) → α₁ Adjeq≃ α₁
  Adjeq≃-idf _ = idp , (idp , idp)

  abstract
    -- eta coherence of Adjeq≃ implies eps coherence
    coher-r-to-coher-l : {α₁ α₂ : Adjequiv f} (e-inv : inv α₁ == inv α₂) →
      (eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂) → (eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps α₂)
    coher-r-to-coher-l {α₁} {α₂} e-inv c = =ₛ-out $
      (eps α₁ ∙' ap (λ m → f ◻ m) e-inv) ◃∎
        =ₛ⟨ =ₛ-in (∙'=∙ (eps α₁) (ap (λ m → f ◻ m) e-inv )) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) e-inv ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ m → f ◻ m) aux2 ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (ap (λ m → m ◻ inv α₁) (eta α₂)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → f ◻ m) (λ m → m ◻ inv α₁) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      ap (λ m → f ◻ m ◻ inv α₁) (eta α₂) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 2 & 1 & hmtpy-nat-∙◃ (λ m → α f m (inv α₁)) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → (f ◻ m) ◻ inv α₁) (eta α₂) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (λ m → m ◻ inv α₁) (λ m → f ◻ m) (eta α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → f ◻ m) (eta α₂)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-=ₛ (λ m → m ◻ inv α₁) (coher-map-rot α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ap (λ m → inv α₂ ◻ m) (eps α₁))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 9 & 1 &
          ap-! (λ m → f ◻ m) (ap (λ m → inv α₂ ◻ m) (eps α₁)) ∙
          ap ! (∘-ap (λ m → f ◻ m) (λ m → inv α₂ ◻ m) (eps α₁) ) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      ! (ap (λ m → f ◻ inv α₂ ◻ m) (eps α₁)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 9 & 1 & hmtpy-nat-∙◃! (λ m → α f (inv α₂) m ∙ ! (ap (λ k → k ◻ m) (eps α₂)) ∙ ! (lamb m)) (eps α₁) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      ! (α f (inv α₂) (id₁ b) ∙
      ! (ap (λ m → m ◻ id₁ b) (eps α₂)) ∙
      ! (lamb (id₁ b))) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 11 & 1 & !-∙-seq (α f (inv α₂) (id₁ b) ◃∙ ! (ap (λ m → m ◻ id₁ b) (eps α₂)) ◃∙ ! (lamb (id₁ b)) ◃∎) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      ! (! (lamb (id₁ b))) ◃∙
      ! (! (ap (λ m → m ◻ id₁ b) (eps α₂))) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₑ⟨ 11 & 2 & (lamb (id₁ b) ◃∙ ap (λ m → m ◻ id₁ b) (eps α₂) ◃∎)
          % =ₛ-in (ap2 _∙_ (!-! (lamb (id₁ b))) (!-! (ap (λ m → m ◻ id₁ b) (eps α₂)))) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      lamb (id₁ b) ◃∙
      ap (λ m → m ◻ id₁ b) (eps α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 12 & 1 & apCommSq◃ ρ (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      lamb (id₁ b) ◃∙
      ! (ρ (id₁ b)) ◃∙
      ap (λ m → m) (eps α₂) ◃∙
      ρ (f ◻ inv α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ₁⟨ 11 & 2 & ap (λ p → p ∙ ! (ρ (id₁ b))) lamb-ρ-id₁-bc ∙ !-inv-r (ρ (id₁ b)) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∙
      ρ (f ◻ inv α₂) ◃∙
      ! (α f (inv α₂) (id₁ b)) ◃∙
      ap (λ m → f ◻ m) (! (ρ (inv α₂))) ◃∎
        =ₛ⟨ 13 & 3 & trig-ρ-bc-rot f (inv α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      (α f (inv α₂) (f ◻ inv α₁) ∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ∙
      ! (lamb (f ◻ inv α₁))) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₑ⟨ 9 & 1 & (α f (inv α₂) (f ◻ inv α₁) ◃∙ ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙ ! (lamb (f ◻ inv α₁)) ◃∎)
          % =ₛ-in idp ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → m ◻ inv α₁) (ap (λ m → m ◻ f) (eps α₂)) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 5 & 1 & ∘-ap (λ m → m ◻ inv α₁) (λ m → m ◻ f) (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ap (λ m → (m ◻ f) ◻ inv α₁) (eps α₂) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 5 & 1 & apCommSq◃ (λ m → α m f (inv α₁)) (eps α₂) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ap (λ m → m ◻ f ◻ inv α₁) (eps α₂) ◃∙
      α (f ◻ (inv α₂)) f (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (α f (inv α₂) f)) ◃∙
      ! (α f (inv α₂ ◻ f) (inv α₁)) ◃∙
      ap (λ m → f ◻ m) (! (α (inv α₂) f (inv α₁))) ◃∙
      α f (inv α₂) (f ◻ inv α₁) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 7 & 5 & pent-bc◃-rot (inv α₁) f (inv α₂) f ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ap (λ m → m ◻ f ◻ inv α₁) (eps α₂) ◃∙
      ! (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 6 & 2 & !-inv-r (ap (λ m → m ◻ f ◻ inv α₁) (eps α₂)) ⟩
      eps α₁ ◃∙
      ap (λ m → f ◻ m) (lamb (inv α₁)) ◃∙
      α f (id₁ a) (inv α₁) ◃∙
      ap (λ m → m ◻ inv α₁) (! (ρ f)) ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      idp ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 1 & 3 & tri-bc◃-rot2 (inv α₁) f ⟩
      eps α₁ ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      idp ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 3 & 2 & idp ⟩
      eps α₁ ◃∙
      ap (λ m → m ◻ inv α₁) (lamb f) ◃∙
      ! (α (id₁ b) f (inv α₁)) ◃∙
      ! (lamb (f ◻ inv α₁)) ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ⟨ 1 & 3 & trig-lamb-bc-rot f (inv α₁) ⟩
      eps α₁ ◃∙
      ! (ap (λ m → m) (eps α₁)) ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ 0 & 2 & !-ap-idf-r (eps α₁) ⟩
      idp ◃∙
      idp ◃∙
      ap (λ m → m) (eps α₂) ◃∎
        =ₛ₁⟨ ap-idf (eps α₂) ⟩
      eps α₂ ◃∎ ∎ₛ

      where

        aux1 : ap (λ m → m ◻ f) e-inv == ! (eta α₁) ∙ eta α₂
        aux1 = ∙'-rot-out (eta α₁) (ap (λ m → m ◻ f) e-inv) c

        aux2 :
          e-inv ◃∎
            =ₛ
          lamb (inv α₁) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
        aux2 = 
          e-inv ◃∎
            =ₛ⟨ =ₛ-in (equiv-adj (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) aux1) ⟩
          ! (! (α (inv α₁) f (inv α₁)) ∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ∙ ! (ρ (inv α₁))) ◃∙
          ap (λ m → m ◻ inv α₁) (! (eta α₁) ∙ eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 1 & 1 & ap-!∙◃ (λ m → m ◻ inv α₁) (eta α₁) (eta α₂) ⟩
          ! (! (α (inv α₁) f (inv α₁)) ∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ∙ ! (ρ (inv α₁))) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 0 & 1 & !-∙-seq (! (α (inv α₁) f (inv α₁)) ◃∙ ! (ap (λ m → inv α₁ ◻ m) (eps α₁)) ◃∙ ! (ρ (inv α₁)) ◃∎) ⟩
          ! (! (ρ (inv α₁))) ◃∙
          ! (! (ap (λ m → inv α₁ ◻ m) (eps α₁))) ◃∙
          ! (! (α (inv α₁) f (inv α₁))) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₑ⟨ 0 & 3 & (ρ (inv α₁) ◃∙ ap (λ m → inv α₁ ◻ m) (eps α₁) ◃∙ α (inv α₁) f (inv α₁) ◃∎)
              % =ₛ-in (ap3 (λ p₁ p₂ p₃ → p₁ ∙ p₂ ∙ p₃)
                (!-! (ρ (inv α₁)))
                (!-! (ap (λ m → inv α₁ ◻ m) (eps α₁)))
                (!-! (α (inv α₁) f (inv α₁)))) ⟩
          ρ (inv α₁) ◃∙
          ap (λ m → inv α₁ ◻ m) (eps α₁) ◃∙
          α (inv α₁) f (inv α₁) ◃∙
          ! (ap (λ m → m ◻ inv α₁) (eta α₁)) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎
            =ₛ⟨ 0 & 4 & coher-inv-rot α₁ ⟩
          lamb (inv α₁) ◃∙
          ap (λ m → m ◻ inv α₁) (eta α₂) ◃∙
          ! (α (inv α₂) f (inv α₁)) ◃∙
          ! (ap (λ m → inv α₂ ◻ m) (eps α₁)) ◃∙
          ! (ρ (inv α₂)) ◃∎ ∎ₛ

  module ae-SIP {α₁ : Adjequiv f} where

    -- SIP for adjoint equivalence structures

    Adjeq≃-contr-aux :
      is-contr $
        [ (inv₂ , e-inv) ∈ Σ (hom b a) (λ inv₂ → inv α₁ == inv₂) ] ×
          [ ((eta₂ , _) , eps₂ , _) ∈
          (Σ (id₁ a == inv₂ ◻ f) (λ eta₂ → eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta₂) ×
          (Σ (id₁ b == f ◻ inv₂) (λ eps₂ → eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps₂))) ] ×
            ((ρ f ∙ ap (λ m → f ◻ m) eta₂ ∙ α f inv₂ f == lamb f ∙ ap (λ m → m ◻ f) eps₂) ×
            (ρ inv₂ ∙ ap (λ m → inv₂ ◻ m) eps₂ ∙ α inv₂ f inv₂ == lamb inv₂ ∙ ap (λ m → m ◻ inv₂) eta₂))
    Adjeq≃-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = Σ (hom b a) (λ inv₂ → inv α₁ == inv₂)} pathfrom-is-contr-instance)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red (×-level pathfrom-is-contr-instance pathfrom-is-contr-instance))⁻¹)
          {{×-level (inhab-prop-is-contr (coher-map α₁)) (inhab-prop-is-contr (coher-inv α₁))}}}}

    abstract
      Adjeq≃-contr : is-contr (Σ (Adjequiv f) (λ α₂ → α₁ Adjeq≃ α₂))
      Adjeq≃-contr = equiv-preserves-level lemma {{Adjeq≃-contr-aux}}
        where
          lemma :
            [ (inv₂ , e-inv) ∈ Σ (hom b a) (λ inv₂ → inv α₁ == inv₂) ] ×
              [ ((eta₂ , _) , eps₂ , _) ∈
              (Σ (id₁ a == inv₂ ◻ f) (λ eta₂ → eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta₂) ×
              (Σ (id₁ b == f ◻ inv₂) (λ eps₂ → eps α₁ ∙' ap (λ m → f ◻ m) e-inv == eps₂))) ] ×
                ((ρ f ∙ ap (λ m → f ◻ m) eta₂ ∙ α f inv₂ f == lamb f ∙ ap (λ m → m ◻ f) eps₂) ×
                (ρ inv₂ ∙ ap (λ m → inv₂ ◻ m) eps₂ ∙ α inv₂ f inv₂ == lamb inv₂ ∙ ap (λ m → m ◻ inv₂) eta₂))
              ≃
            Σ (Adjequiv f) (λ α₂ → α₁ Adjeq≃ α₂)
          lemma =
            equiv
              (λ ((inv₂ , e-inv) , ((eta₂ , e-eta) , (eps₂ , e-eps)) , (cm₂ , ci₂)) → (Adj-eqv inv₂ eta₂ eps₂ cm₂ ci₂) , e-inv , (e-eta , e-eps))
              (λ ((Adj-eqv inv₂ eta₂ eps₂ cm₂ ci₂) , e-inv , (e-eta , e-eps)) → (inv₂ , e-inv) , ((eta₂ , e-eta) , (eps₂ , e-eps)) , (cm₂ , ci₂))
              (λ _ → idp)
              λ _ → idp

    Adjeq≃-ind : ∀ {k} (P : (α₂ : Adjequiv f) → (α₁ Adjeq≃ α₂ → Type k))
      → P α₁ (Adjeq≃-idf α₁) → {α₂ : Adjequiv f} (e : α₁ Adjeq≃ α₂) → P α₂ e
    Adjeq≃-ind P = ID-ind-map P Adjeq≃-contr

    Adjeq≃-ind-β : ∀ {k} (P : (α₂ : Adjequiv f) → (α₁ Adjeq≃ α₂ → Type k))
      → (r : P α₁ (Adjeq≃-idf α₁)) → Adjeq≃-ind P r (Adjeq≃-idf α₁) == r
    Adjeq≃-ind-β P = ID-ind-map-β P Adjeq≃-contr

    Adjeq≃-to-== : {α₂ : Adjequiv f} → α₁ Adjeq≃ α₂ → α₁ == α₂ 
    Adjeq≃-to-== = Adjeq≃-ind (λ α₂ _ → α₁ == α₂) idp

  -- being an adjoint equivalence is a proposition

    Adjequiv-unique : {α₂ : Adjequiv f} → α₁ == α₂
    Adjequiv-unique {α₂} =  Adjeq≃-to-==
      (e-inv , coher , coher-r-to-coher-l {α₁} {α₂} e-inv coher)
      where

        e-inv : inv α₁ == inv α₂
        e-inv = <– (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) (! (eta α₁) ∙ eta α₂) 

        coher : eta α₁ ∙' ap (λ m → m ◻ f) e-inv == eta α₂
        coher =
          ∙'=∙ (eta α₁) (ap (λ m → m ◻ f) e-inv) ∙
          ap (λ p → eta α₁ ∙ p) (<–-inv-r (ap-equiv (Adjequiv-whisk-r-≃ α₁) _ _) (! (eta α₁) ∙ eta α₂)) ∙
          assoc-inv-l  (eta α₁) (eta α₂)  

  instance
    Adjequiv-is-prop : is-prop (Adjequiv f)
    Adjequiv-is-prop = all-paths-is-prop λ _ _ → Adjequiv-unique where open ae-SIP
