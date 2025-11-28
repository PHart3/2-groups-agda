{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.wild-cats.WildCats
open import Bicategory
open import AdjEq
open import Bicat-wild
open import Biadj
open import Pstransf-SIP
open import Univ-bc
open import Bicat-iso
open import Psftor-inverse
open import Psftor-laws

module Biequiv where

open BicatStr {{...}}

open import Pstransf public
open Pstrans

module _ {i₁ i₂ j₁ j₂} {C₀ : Type i₂} {B₀ : Type i₁}  where

  -- biequivalence structure between two bicats
  
  record BiequivStr-inst {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}} : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor bequiv
    field
      Ψ-L : Psfunctor {{ξB}} {{ξC}}
      Ψ-R : Psfunctor {{ξC}} {{ξB}}
      ε : (psftor-str (Ψ-L ∘BC Ψ-R)) ps-≃ idpfBC
      η : idpfBC ps-≃ (psftor-str (Ψ-R ∘BC Ψ-L))

    τ₁ : Pstrans (psftor-str (Ψ-L ∘BC Ψ-R)) idpfBC
    τ₁ = fst ε

    τ₂ : Pstrans idpfBC (psftor-str (Ψ-R ∘BC Ψ-L))
    τ₂ = fst η

    lev-eq₁ : (a : C₀) → Adjequiv {{ξC}} (η₀ τ₁ a)
    lev-eq₁ a = snd ε a

    lev-eq₂ : (a : B₀) → Adjequiv {{ξB}} (η₀ τ₂ a)
    lev-eq₂ a = snd η a

  -- for clarity of final theorem statement
  BiequivStr : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → Type (lmax (lmax i₁ j₁) (lmax i₂ j₂))
  BiequivStr ξC ξB = BiequivStr-inst {{ξC}} {{ξB}}

  -- biadjoint biequivalences (between univalent bicategories)
  infixr 70 _biadj-bieqv_
  _biadj-bieqv_ : (ξC : BicatStr j₂ C₀) (ξB : BicatStr j₁ B₀) → {{is-univ-bc-inst {{ξC}}}} → {{is-univ-bc-inst {{ξB}}}}
    → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  ξC biadj-bieqv ξB = Σ (BiequivStr ξC ξB) (λ be →
    Biequiv-coh {{ξC}} {{ξB}} {R = Ψ-R {{ξC}} {{ξB}} be} {L = Ψ-L {{ξC}} {{ξB}} be}
      (ε {{ξC}} {{ξB}} be) (η {{ξC}} {{ξB}} be)) where open BiequivStr-inst

  is-biadj-bieqv : {{ξC : BicatStr j₂ C₀}} {{ξB : BicatStr j₁ B₀}}
    {{uC : is-univ-bc-inst {{ξC}}}} {{uB : is-univ-bc-inst {{ξB}}}}
    → Psfunctor {{ξC}} {{ξB}} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-biadj-bieqv R = Σ (has-rinv-psf R) (psft-rinv-coh-data {R = R})

open BiequivStr-inst
open Biequiv-coh
open InvMod

-- the identity biadjoint biequivalence
biadj-bieuqiv-id : ∀ {i j} {C₀ : Type i} {{ξC : BicatStr j C₀}} {{uC : is-univ-bc-inst {{ξC}}}} → ξC biadj-bieqv ξC
Ψ-L (fst biadj-bieuqiv-id) = idfBC
Ψ-R (fst biadj-bieuqiv-id) = idfBC
ε (fst biadj-bieuqiv-id) = unitl-ps-≃ idpfBC
η (fst biadj-bieuqiv-id) = unitr-ps-≃ idpfBC
η₀-∼ (ζζ (snd (biadj-bieuqiv-id {{ξC}}))) a = ! (ap (λ m → ⟦ ξC ⟧ m ◻ id₁ ξC a) (lamb ξC (id₁ ξC a)))
η₁-∼ (ζζ (snd (biadj-bieuqiv-id {{ξC}}))) {a} {b} f = {!=ₛ-out $
  ! (α ξC f ((ξC ◻ id₁ ξC a) (id₁ ξC a)) (id₁ ξC a) ∙
  ap (λ m → (ξC ◻ m) (id₁ ξC a))
    (α ξC f (id₁ ξC a) (id₁ ξC a) ∙
    ap (λ m → (ξC ◻ m) (id₁ ξC a)) (ap (λ m → m) (! (ρ ξC f) ∙ lamb ξC f) ∙ idp) ∙
    ! (α ξC (id₁ ξC b) f (id₁ ξC a)) ∙
    ap (λ m → (ξC ◻ id₁ ξC b) m) (! (ρ ξC f) ∙ lamb ξC f) ∙
    α ξC (id₁ ξC b) (id₁ ξC b) f) ∙
  ! (α ξC ((ξC ◻ id₁ ξC b) (id₁ ξC b)) f (id₁ ξC a)) ∙
  ap (λ m → (ξC ◻ (ξC ◻ id₁ ξC b) (id₁ ξC b)) m) (! (ρ ξC f) ∙ lamb ξC f) ∙
  α ξC ((ξC ◻ id₁ ξC b) (id₁ ξC b)) (id₁ ξC b) f) ◃∙
  ap (ξC ◻ f) (! (ap (λ m → (ξC ◻ m) (id₁ ξC a)) (lamb ξC (id₁ ξC a)))) ◃∙
  (α ξC f (id₁ ξC a) (id₁ ξC a) ∙
  ap (λ m → (ξC ◻ m) (id₁ ξC a)) (! (ρ ξC f) ∙ lamb ξC f) ∙
  ! (α ξC (id₁ ξC b) f (id₁ ξC a)) ∙
  ap (λ m → (ξC ◻ id₁ ξC b) m) (! (ρ ξC f) ∙ lamb ξC f) ∙
  α ξC (id₁ ξC b) (id₁ ξC b) f) ◃∙
  ! (ap (λ m → (ξC ◻ m) f) (! (ap (λ m → (ξC ◻ m) (id₁ ξC b)) (lamb ξC (id₁ ξC b))))) ◃∎
    =ₛ⟨ ? ⟩
  ?!}
  
module _ {i₁ i₂ j₁ j₂} {C@(C₀ , _) : Bicat j₂ i₂} {B@(B₀ , _) : Bicat j₁ i₁} where

  private
    instance
      ξC : BicatStr j₂ C₀
      ξC = snd C
      ξB : BicatStr j₁ B₀
      ξB = snd B
     
  open Equiv-wc

  -- every biequivalence induces an equivalence of wild categories
  beqv-to-wniso : BiequivStr ξC ξB → Equiv-wc (bc-to-wc B) (bc-to-wc C)
  ftor₁ (beqv-to-wniso be) = pf-to-wf (psftor-str (Ψ-L be))
  ftor₂ (beqv-to-wniso be) = pf-to-wf (psftor-str (Ψ-R be))
  fst (iso₁ (beqv-to-wniso be)) = ptr-to-ntr (τ₁ be)
  snd (iso₁ (beqv-to-wniso be)) x = aeqv-to-weqv (lev-eq₁ be x)
  fst (iso₂ (beqv-to-wniso be)) = ptr-to-ntr (τ₂ be)
  snd (iso₂ (beqv-to-wniso be)) x = aeqv-to-weqv (lev-eq₂ be x)

  module _ {{_ : is-univ-bc-inst {{ξC}}}} {{_ : is-univ-bc-inst {{ξB}}}} where

    open Psfunctor
    open PsfunctorStr
    open HAdjEquiv-wc

    baeqv-to-wniso : ξC biadj-bieqv ξB → HAdjEquiv-wc (bc-to-wc B) (bc-to-wc C)
    𝔼 (baeqv-to-wniso (be , _)) = beqv-to-wniso be
    zig-zag (baeqv-to-wniso (be , ba)) x =
      ap (λ m → m ◻ η₀ (τ₂ be) (map-pf (Ψ-R be) x)) (ρ ξB (F₁ (str-pf (Ψ-R be)) (η₀ (τ₁ be) x)))  ∙
      η₀-∼ (ζζ ba) x ∙
      ! (lamb ξB (id₁ ξB (map-pf (Ψ-R be) x)))

    -- Both pseudofunctors of a biadjoint biequivalence are fully faithful.
    
    baeqv-is-ff-R : ((be , _) : ξC biadj-bieqv ξB) → (x y : C₀) → is-equiv (F₁ (str-pf (Ψ-R be)) {x} {y})
    baeqv-is-ff-R bae _ _ = HAEquiv-wc-ff-R {C = bc-to-wc B} {D = bc-to-wc C} (baeqv-to-wniso bae)

    baeqv-is-ff-L : ((be , _) : ξC biadj-bieqv ξB) → (x y : B₀) → is-equiv (F₁ (str-pf (Ψ-L be)) {x} {y})
    baeqv-is-ff-L bae _ _ = HAEquiv-wc-ff-L {C = bc-to-wc B} {D = bc-to-wc C} (baeqv-to-wniso bae)

    -- being a biadjoint biequivalence is a mere proposition
    abstract
      biadjequiv-is-prop : {R : Psfunctor {{ξC}} {{ξB}}} → is-prop (is-biadj-bieqv R)
      biadjequiv-is-prop {R} = inhab-to-contr-is-prop λ ((L , η) , (ε , _))
        → Σ-level (psf-hi-rinv-contr {R = R} (L , (ε , η))) λ η' →
          bae-rinv-cd-contr {R = R} {fst η'} (transport (λ m → psftor-str (m ∘BC R) ps-≃ idpfBC)
            (psf-has-rinv-unique {R = R} (L , (ε , η)) {R₁ = L} {R₂ = fst η'} η (snd η')) ε) (snd η')

    is-biadj-bieqv-tot : Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
    is-biadj-bieqv-tot = Σ (Psfunctor {{ξC}} {{ξB}}) is-biadj-bieqv

    bae-tot-≃ : ξC biadj-bieqv ξB ≃ is-biadj-bieqv-tot
    bae-tot-≃ = equiv
      (λ (bes , c) → (Ψ-R bes) , (((Ψ-L bes) , (η bes)) , (ε bes , ζζ c)))
      (λ (ψR , ((ψL , eta) , (eps , zz))) → (bequiv ψL ψR eps eta) , bieqvcoh zz)
      (λ _ → idp)
      λ _ → idp

module _ {i j} {C₀ B₀ : Type i} {{ξC : BicatStr j C₀}} {{ξB : BicatStr j B₀}}
  {{uC : is-univ-bc-inst {{ξC}}}} {{uB : is-univ-bc-inst {{ξB}}}} where

  private
  
    C : Bicat j i
    C = (C₀ , ξC)

    B : Bicat j i
    B = (B₀ , ξB)

  bae-tot-iso : is-biadj-bieqv-tot ≃ ξC iso-bc ξB
  bae-tot-iso = Σ-emap-r (λ R → props-BiImp-≃ {{biadjequiv-is-prop {R = R}}} {{iso-bc-is-prop {φ = R}}}
    (forw R) λ iso → backw (R , iso))
    where
    
      open Psfunctor
      forw : (R : Psfunctor {{ξC}} {{ξB}}) → is-biadj-bieqv R → is-iso-bc R
      fst (forw R ((L , ri) , li , _)) = is-eq (map-pf R) (map-pf L)
        (λ b → ! (ubc-ae-to-== ((η₀ (fst ri) b) , (snd ri b))))
        λ c → ubc-ae-to-== ((η₀ (fst li) c) , (snd li c))
      snd (forw R is-bae) = baeqv-is-ff-R (<– bae-tot-≃ (R , is-bae))

      backw : {(_ , ξE) : Bicat j i} (iso : ξC iso-bc ξE) →
        {{_ : is-univ-bc-inst {{ξE}}}} → is-biadj-bieqv {{ξB = ξE}} (fst iso)
      backw = bc-ind ξC (λ E iso → ∀ {{uE : is-univ-bc-inst {{snd E}}}} →
        is-biadj-bieqv {{ξB = snd E}} {{uB = uE}} (fst iso)) λ {{_}} →
          snd (–> bae-tot-≃  (biadj-bieuqiv-id {{uC = uC}}))

  -- biadjoint equivalences are equivalent to isomorphisms, hence identities

  bae-iso-≃ : ξC biadj-bieqv ξB ≃ ξC iso-bc ξB
  bae-iso-≃ = bae-tot-iso ∘e bae-tot-≃

  bae-==-≃ : (ξC biadj-bieqv ξB) ≃ (C == B)
  bae-==-≃ = iso-bc-==-≃ ∘e bae-tot-iso ∘e bae-tot-≃ 

  -- ψ-R induces an equalities between bicategories
  baequiv-to-==-R : ξC biadj-bieqv ξB → C == B
  baequiv-to-==-R bae = –> bae-==-≃ bae
