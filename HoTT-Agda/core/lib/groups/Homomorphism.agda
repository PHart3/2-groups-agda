{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.Function2
open import lib.NType2
open import lib.types.Coproduct
open import lib.types.Fin
open import lib.types.Group
open import lib.types.Int
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Truncation

module lib.groups.Homomorphism where

{-
Group homomorphisms.
-}

preserves-comp : ∀ {i j} {A : Type i} {B : Type j}
  (A-comp : A → A → A) (B-comp : B → B → B) (f : A → B)
  → Type (lmax i j)
preserves-comp Ac Bc f = ∀ a₁ a₂ → f (Ac a₁ a₂) == Bc (f a₁) (f a₂)

preserves-comp-prop : ∀ {i j} {A : Type i} {B : Type j}
  {{_ : is-set B}} (A-comp : A → A → A) (B-comp : B → B → B)
  → SubtypeProp {A = A → B}
preserves-comp-prop Ac Bc =
  subtypeprop (preserves-comp Ac Bc)

abstract
  ∼-preserves-preserves-comp : ∀ {i j} {A : Type i} {B : Type j}
    (A-comp : A → A → A) (B-comp : B → B → B) {f₀ f₁ : A → B} → f₀ ∼ f₁
    → preserves-comp A-comp B-comp f₀
    → preserves-comp A-comp B-comp f₁
  ∼-preserves-preserves-comp Ac Bc {f₀ = f₀} {f₁} f₀∼f₁ f₀-pc a₁ a₂ =
    ! (f₀∼f₁ (Ac a₁ a₂)) ∙ f₀-pc a₁ a₂ ∙ ap2 Bc (f₀∼f₁ a₁) (f₀∼f₁ a₂)

record GroupStructureHom {i j} {GEl : Type i} {HEl : Type j}
  (GS : GroupStructure GEl) (HS : GroupStructure HEl) : Type (lmax i j) where
  constructor group-structure-hom
  private
    module G = GroupStructure GS
    module H = GroupStructure HS
  field
    f : GEl → HEl
    pres-comp : preserves-comp G.comp H.comp f

  abstract
    pres-ident : f G.ident == H.ident
    pres-ident = H.cancel-l (f G.ident) $
      H.comp (f G.ident) (f G.ident)
        =⟨ ! (pres-comp G.ident G.ident) ⟩
      f (G.comp G.ident G.ident)
        =⟨ ap f (G.unit-l G.ident) ⟩
      f G.ident
        =⟨ ! (H.unit-r (f G.ident)) ⟩
      H.comp (f G.ident) H.ident =∎

    pres-inv : ∀ g → f (G.inv g) == H.inv (f g)
    pres-inv g = ! $ H.inv-unique-l _ _ $
      H.comp (f (G.inv g)) (f g)
        =⟨ ! (pres-comp (G.inv g) g) ⟩
      f (G.comp (G.inv g) g)
        =⟨ ap f (G.inv-l g) ⟩
      f G.ident
        =⟨ pres-ident ⟩
      H.ident
        =∎

    pres-exp : ∀ g i → f (G.exp g i) == H.exp (f g) i
    pres-exp g (pos O) = pres-ident
    pres-exp g (pos (S O)) = idp
    pres-exp g (pos (S (S n))) = pres-comp g (G.exp g (pos (S n))) ∙ ap (H.comp (f g)) (pres-exp g (pos (S n)))
    pres-exp g (negsucc O) = pres-inv g
    pres-exp g (negsucc (S n)) = pres-comp (G.inv g) (G.exp g (negsucc n)) ∙ ap2 H.comp (pres-inv g) (pres-exp g (negsucc n))

    pres-conj : ∀ g h → f (G.conj g h) == H.conj (f g) (f h)
    pres-conj g h = pres-comp (G.comp g h) (G.inv g) ∙ ap2 H.comp (pres-comp g h) (pres-inv g)

    pres-diff : ∀ g h → f (G.diff g h) == H.diff (f g) (f h)
    pres-diff g h = pres-comp g (G.inv h) ∙ ap (H.comp (f g)) (pres-inv h)

    pres-sum : ∀ {I : ℕ} (g : Fin I → GEl) → f (G.sum g) == H.sum (f ∘ g)
    pres-sum {I = O} _ = pres-ident
    pres-sum {I = S _} g = pres-comp (G.sum (g ∘ Fin-S)) (g (_ , ltS))
      ∙ ap (λ h → H.comp h (f (g (_ , ltS)))) (pres-sum (g ∘ Fin-S))

    pres-subsum-r : ∀ {k l} {I : ℕ} {A : Type k} {B : Type l}
      → (p : Fin I → Coprod A B) (g : B → GEl)
      → f (G.subsum-r p g) == H.subsum-r p (f ∘ g)
    pres-subsum-r p g = pres-sum (Coprod-rec (λ _ → G.ident) g ∘ p)
      ∙ ap H.sum (λ= λ x →
            Coprod-rec-post∘ f (λ _ → G.ident) g (p x)
          ∙ ap (λ h → Coprod-rec h (f ∘ g) (p x)) (λ= λ _ → pres-ident))

  ⊙f : ⊙[ GEl , G.ident ] ⊙→ ⊙[ HEl , H.ident ]
  ⊙f = f , pres-ident

infix 0 _→ᴳˢ_ -- [ˢ] for structures
_→ᴳˢ_ = GroupStructureHom

record GroupHom {i j} (G : Group i) (H : Group j) : Type (lmax i j) where
  constructor group-hom
  private
    module G = Group G
    module H = Group H
  field
    f : G.El → H.El
    pres-comp : ∀ g₁ g₂ → f (G.comp g₁ g₂) == H.comp (f g₁) (f g₂)
  open GroupStructureHom {GS = G.group-struct} {HS = H.group-struct}
    record {f = f ; pres-comp = pres-comp} hiding (f ; pres-comp) public

infix 0 _→ᴳ_
_→ᴳ_ = GroupHom

→ᴳˢ-to-→ᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (Group.group-struct G →ᴳˢ Group.group-struct H) → (G →ᴳ H)
→ᴳˢ-to-→ᴳ (group-structure-hom f pres-comp) = group-hom f pres-comp

idhom : ∀ {i} (G : Group i) → (G →ᴳ G)
idhom G = group-hom (idf _) (λ _ _ → idp)

idshom : ∀ {i} {GEl : Type i} (GS : GroupStructure GEl) → (GS →ᴳˢ GS)
idshom GS = group-structure-hom (idf _) (λ _ _ → idp)

{- constant (zero) homomorphism -}
module _ where
  cst-hom : ∀ {i j} {G : Group i} {H : Group j} → (G →ᴳ H)
  cst-hom {H = H} = group-hom (cst (Group.ident H)) (λ _ _ → ! (Group.unit-l H _))

{- negation is a homomorphism in an abelian group -}
inv-hom : ∀ {i} (G : AbGroup i) → GroupHom (AbGroup.grp G) (AbGroup.grp G)
inv-hom G = group-hom G.inv inv-pres-comp where
  module G = AbGroup G
  abstract
    inv-pres-comp : (g₁ g₂ : G.El) → G.inv (G.comp g₁ g₂) == G.comp (G.inv g₁) (G.inv g₂)
    inv-pres-comp g₁ g₂ = G.inv-comp g₁ g₂ ∙ G.comm (G.inv g₂) (G.inv g₁)

{- equality of homomorphisms -}
abstract
  group-hom= : ∀ {i j} {G : Group i} {H : Group j} {φ ψ : G →ᴳ H}
    → GroupHom.f φ == GroupHom.f ψ → φ == ψ
  group-hom= {G = G} {H = H} p = ap (uncurry group-hom) $
    Subtype=-out (preserves-comp-prop (Group.comp G) (Group.comp H)) p

  group-hom=-↓ : ∀ {i j k} {A : Type i} {G : A → Group j} {H : A → Group k} {x y : A}
    {p : x == y} {φ : G x →ᴳ H x} {ψ : G y →ᴳ H y}
    → GroupHom.f φ == GroupHom.f ψ
      [ (λ a → Group.El (G a) → Group.El (H a)) ↓ p ]
    → φ == ψ [ (λ a → G a →ᴳ H a) ↓ p ]
  group-hom=-↓ {p = idp} = group-hom=

abstract
  instance
    GroupHom-level : ∀ {i j} {G : Group i} {H : Group j} → is-set (G →ᴳ H)
    GroupHom-level {G = G} {H = H} = equiv-preserves-level
      (equiv (uncurry group-hom) (λ x → GroupHom.f x , GroupHom.pres-comp x)
             (λ _ → idp) (λ _ → idp))
      {{Subtype-level
        (preserves-comp-prop (Group.comp G) (Group.comp H))}}

infixr 80 _∘ᴳˢ_ _∘ᴳ_

abstract
  ∘ᴳˢ-pres-comp : ∀ {i j k} {GEl : Type i} {HEl : Type j} {KEl : Type k}
    {GS : GroupStructure GEl} {HS : GroupStructure HEl} {KS : GroupStructure KEl}
    (ψ : HS →ᴳˢ KS) (φ : GS →ᴳˢ HS)
    → preserves-comp (GroupStructure.comp GS) (GroupStructure.comp KS) (GroupStructureHom.f ψ ∘ GroupStructureHom.f φ)
  ∘ᴳˢ-pres-comp ψ φ g₁ g₂ = ap (GroupStructureHom.f ψ) (GroupStructureHom.pres-comp φ g₁ g₂)
    ∙ GroupStructureHom.pres-comp ψ (GroupStructureHom.f φ g₁) (GroupStructureHom.f φ g₂)

  ∘ᴳ-pres-comp : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k} (ψ : H →ᴳ K) (φ : G →ᴳ H)
    → preserves-comp (Group.comp G) (Group.comp K) (GroupHom.f ψ ∘ GroupHom.f φ)
  ∘ᴳ-pres-comp ψ φ g₁ g₂ = ap (GroupHom.f ψ) (GroupHom.pres-comp φ g₁ g₂)
    ∙ GroupHom.pres-comp ψ (GroupHom.f φ g₁) (GroupHom.f φ g₂)

_∘ᴳˢ_ : ∀  {i j k} {GEl : Type i} {HEl : Type j} {KEl : Type k}
  {GS : GroupStructure GEl} {HS : GroupStructure HEl} {KS : GroupStructure KEl}
  → (HS →ᴳˢ KS) → (GS →ᴳˢ HS) → (GS →ᴳˢ KS)
ψ ∘ᴳˢ φ = group-structure-hom (GroupStructureHom.f ψ ∘ GroupStructureHom.f φ) (∘ᴳˢ-pres-comp ψ φ)

_∘ᴳ_ : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → (H →ᴳ K) → (G →ᴳ H) → (G →ᴳ K)
ψ ∘ᴳ φ = group-hom (GroupHom.f ψ ∘ GroupHom.f φ) (∘ᴳ-pres-comp ψ φ)

{- algebraic properties -}

∘ᴳ-unit-r : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → φ ∘ᴳ idhom G == φ
∘ᴳ-unit-r φ = group-hom= idp

∘ᴳ-unit-l : ∀ {i j} {G : Group i} {H : Group j} (φ : G →ᴳ H)
  → idhom H ∘ᴳ φ == φ
∘ᴳ-unit-l φ = group-hom= idp

∘ᴳ-assoc : ∀ {i j k l} {G : Group i} {H : Group j} {K : Group k} {L : Group l}
  (χ : K →ᴳ L) (ψ : H →ᴳ K) (φ : G →ᴳ H)
  → (χ ∘ᴳ ψ) ∘ᴳ φ == χ ∘ᴳ ψ ∘ᴳ φ
∘ᴳ-assoc χ ψ φ = group-hom= idp

is-injᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (G →ᴳ H) → Type (lmax i j)
is-injᴳ hom = is-inj (GroupHom.f hom)

is-surjᴳ : ∀ {i j} {G : Group i} {H : Group j}
  → (G →ᴳ H) → Type (lmax i j)
is-surjᴳ hom = is-surj (GroupHom.f hom)

{- homomorphisms into an abelian group can be composed with
 - the group operation and form a group -}
module _ {i j} (G : Group i) (H : AbGroup j)
  where

  private
    module G = Group G
    module H = AbGroup H

  abstract
    hom-comp-pres-comp : (φ : G →ᴳ H.grp) → (ψ : G →ᴳ H.grp) → (g₁ : _) (g₂ : _)
        →  H.comp (GroupHom.f φ (G.comp g₁ g₂)) (GroupHom.f ψ (G.comp g₁ g₂))
        == H.comp (H.comp (GroupHom.f φ g₁) (GroupHom.f ψ g₁)) (H.comp (GroupHom.f φ g₂) (GroupHom.f ψ g₂))
    hom-comp-pres-comp φ ψ g₁ g₂ =
        H.comp (φ.f (G.comp g₁ g₂)) (ψ.f (G.comp g₁ g₂))
          =⟨ ap2 H.comp (φ.pres-comp g₁ g₂) (ψ.pres-comp g₁ g₂) ⟩
        H.comp (H.comp (φ.f g₁) (φ.f g₂)) (H.comp (ψ.f g₁) (ψ.f g₂))
          =⟨ H.interchange (φ.f g₁) (φ.f g₂) (ψ.f g₁) (ψ.f g₂) ⟩
        H.comp (H.comp (φ.f g₁) (ψ.f g₁)) (H.comp (φ.f g₂) (ψ.f g₂)) =∎
        where
          module φ = GroupHom φ
          module ψ = GroupHom ψ


  hom-comp : (G →ᴳ H.grp) → (G →ᴳ H.grp) → (G →ᴳ H.grp)
  hom-comp φ ψ = group-hom (λ g → H.comp (GroupHom.f φ g) (GroupHom.f ψ g)) (hom-comp-pres-comp φ ψ)

  hom-group-structure : GroupStructure (G →ᴳ H.grp)
  hom-group-structure = record {M} where
    module M where
      ident : G →ᴳ H.grp
      ident = cst-hom

      comp : (G →ᴳ H.grp) → (G →ᴳ H.grp) → (G →ᴳ H.grp)
      comp = hom-comp

      inv : (G →ᴳ H.grp) → (G →ᴳ H.grp)
      inv φ = inv-hom H ∘ᴳ φ

      abstract
        unit-l : ∀ φ → comp ident φ == φ
        unit-l φ = group-hom= $ λ= λ _ → H.unit-l _

        assoc : ∀ φ ψ ξ → comp (comp φ ψ) ξ == comp φ (comp ψ ξ)
        assoc φ ψ ξ = group-hom= $ λ= λ _ → H.assoc _ _ _

        inv-l : ∀ φ → comp (inv φ) φ == ident
        inv-l φ = group-hom= $ λ= λ _ → H.inv-l _

  hom-group : Group (lmax i j)
  hom-group = group (G →ᴳ H.grp) hom-group-structure

  abstract
    hom-group-is-abelian : is-abelian hom-group
    hom-group-is-abelian φ ψ = group-hom= $ λ= λ g → H.comm _ _

  hom-abgroup : AbGroup (lmax i j)
  hom-abgroup = hom-group , hom-group-is-abelian

module _ {i j} {G : Group i} {H : AbGroup j} where
  app-hom : Group.El G → hom-group G H →ᴳ AbGroup.grp H
  app-hom g = group-hom (λ φ → GroupHom.f φ g) lemma
    where
      abstract
        lemma : (φ ψ : Group.El (hom-group G H)) →
                GroupHom.f (Group.comp (hom-group G H) φ ψ) g ==
                GroupHom.f (Group.comp (hom-group G H) φ ψ) g
        lemma = λ φ ψ → idp

  appᴳ = app-hom

pre∘ᴳ-hom : ∀ {i j k} {G : Group i} {H : Group j} (K : AbGroup k)
  → (G →ᴳ H) → (hom-group H K →ᴳ hom-group G K)
pre∘ᴳ-hom {G = G} {H = H} K φ = record { f = _∘ᴳ φ ; pres-comp = lemma}
  where
    abstract
      lemma : (z₁ z₂ : Group.El (hom-group H K)) →
              Group.comp (hom-group H K) z₁ z₂ ∘ᴳ φ ==
              group-hom (GroupHom.f (Group.comp (hom-group H K) z₁ z₂ ∘ᴳ φ))
              (hom-comp-pres-comp G K (z₁ ∘ᴳ φ) (z₂ ∘ᴳ φ))
      lemma = λ _ _ → group-hom= idp

post∘ᴳ-hom : ∀ {i j k} (G : Group i) (H : AbGroup j) (K : AbGroup k)
  → (AbGroup.grp H →ᴳ AbGroup.grp K) → (hom-group G H →ᴳ hom-group G K)
post∘ᴳ-hom {i} {j} {k} G H K φ = record { f = φ ∘ᴳ_ ; pres-comp = lemma}
  where
    abstract
      lemma : (z₁ z₂ : Group.El (hom-group {i} {j} G H)) →
            _==_ {lmax i k} {GroupHom {i} {k} G (fst K)}
            (group-hom
            (λ z₃ →
              GroupHom.f φ
              (Group.comp {j} (AbGroup.grp {j} H) (GroupHom.f z₁ z₃)
            (GroupHom.f z₂ z₃)))
            (∘ᴳ-pres-comp {i} {j} {k} {G} {AbGroup.grp {j} H}
            {AbGroup.grp {k} K} φ
            (Group.comp {lmax i j} (hom-group {i} {j} G H) z₁ z₂)))
            (group-hom
            (λ z₃ →
              GroupStructure.comp (Group.group-struct (fst K))
            (GroupHom.f φ (GroupHom.f z₁ z₃))
            (GroupHom.f φ (GroupHom.f z₂ z₃)))
            (hom-comp-pres-comp {i} {k} G K
            (_∘ᴳ_ {i} {j} {k} {G} {AbGroup.grp {j} H} {AbGroup.grp {k} K} φ z₁)
            (_∘ᴳ_ {i} {j} {k} {G} {AbGroup.grp {j} H} {AbGroup.grp {k} K} φ z₂)))
      lemma = λ _ _ → group-hom= $ λ= λ _ → GroupHom.pres-comp φ _ _
