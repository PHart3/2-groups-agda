{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma
open import 2MagMap
open import 2Grp
open import NatIso

module 2GrpMap where

open CohGrp {{...}}
open WkMagHomStr
open CohGrpHom
open WkMagNatIso

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  WkMagNatIso-forg : (f g : CohGrpHom {{η₁}} {{η₂}}) → Type (lmax i j)
  WkMagNatIso-forg f g = WkMagNatIso (grphom-forg f) (grphom-forg g)

  natiso-id2G : (μ : CohGrpHom {{η₁}} {{η₂}}) → WkMagNatIso-forg μ μ
  natiso-id2G μ = natiso-id (grphom-forg μ)

-- induction principle for nat isos between 2-groups
module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  module _ {μ : CohGrpHom {{η₁}} {{η₂}}} where

    natiso2G-contr-aux :
       is-contr
         (Σ (Σ (G₁ → G₂) (λ f → map μ ∼ f))
           (λ (f , H) →
             Σ (Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
                 (λ c → ((x , y) : G₁ × G₁) →
                   c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk (grphom-forg μ)) (x , y) ∙ H (mu x y)))
               (λ (map-comp' , c) → (x y z : G₁) → 
                 ! (al (f x) (f y) (f z)) ∙
                 ap (mu (f x)) (map-comp' (y , z)) ∙
                 map-comp' (x , (mu y z))
                   ==
                 ap (λ v → mu v (f z)) (map-comp' (x , y)) ∙
                 map-comp' ((mu x y) , z) ∙
                 ! (ap f (al x y z)))))
    natiso2G-contr-aux = equiv-preserves-level (
      (Σ-contr-red
        {P =
          λ (f , H) →
             Σ (Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
                 (λ c → ((x , y) : G₁ × G₁) →
                   c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk (grphom-forg μ)) (x , y) ∙ H (mu x y)))
               (λ (map-comp' , _) → (x y z : G₁) → 
                 ! (al (f x) (f y) (f z)) ∙
                 ap (mu (f x)) (map-comp' (y , z)) ∙
                 map-comp' (x , (mu y z))
                   ==
                 ap (λ v → mu v (f z)) (map-comp' (x , y)) ∙
                 map-comp' ((mu x y) , z) ∙
                 ! (ap f (al x y z)))}
        (funhom-contr {f = map μ}))⁻¹ )
      {{equiv-preserves-level (
        (Σ-contr-red
          {A =
            (Σ (((x , y) : G₁ × G₁) → mu (map μ x) (map μ y) == map μ (mu x y))
              (λ c → ((x , y) : G₁ × G₁) →
                c (x , y) == ! (ap2 mu idp idp) ∙ uncurry (map-comp-wk (grphom-forg μ)) (x , y) ∙ idp))}
          (equiv-preserves-level
            ((Σ-emap-r
              (λ c → Π-emap-r (λ (x , y) → post∙-equiv (! (∙-unit-r (map-comp-wk (grphom-forg μ) x y)))) ∘e app=-equiv)))
            {{pathto-is-contr (uncurry (map-comp-wk (grphom-forg μ)))}}))⁻¹ )
        {{inhab-prop-is-contr (map-al (str μ))}}}} 

    abstract
      natiso2G-contr : is-contr (Σ (CohGrpHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso-forg μ ν))
      natiso2G-contr = equiv-preserves-level aux {{natiso2G-contr-aux}}
        where
          aux : 
            Σ (Σ (G₁ → G₂) (λ f → map μ ∼ f))
              (λ (f , H) →
                Σ (Σ (((x , y) : G₁ × G₁) → mu (f x) (f y) == f (mu x y))
                    (λ c → ((x , y) : G₁ × G₁) →
                      c (x , y) == ! (ap2 mu (H x) (H y)) ∙ uncurry (map-comp-wk (grphom-forg μ)) (x , y) ∙ H (mu x y)))
                  (λ (map-comp' , _) → (x y z : G₁) → 
                    ! (al (f x) (f y) (f z)) ∙
                    ap (mu (f x)) (map-comp' (y , z)) ∙
                    map-comp' (x , (mu y z))
                      ==
                    ap (λ v → mu v (f z)) (map-comp' (x , y)) ∙
                    map-comp' ((mu x y) , z) ∙
                    ! (ap f (al x y z))))
            ≃
            Σ (CohGrpHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso-forg μ ν)
          aux = 
            equiv
              (λ ((f , H) , (map-comp' , c) , al) → (cohgrphom f {{cohmaghomstr (curry map-comp') al}}) ,
                cohgrpnatiso H (curry c))
              (λ (ν , iso) → ((map ν) , (θ iso)) , (((uncurry (map-comp (str ν))) , (uncurry (θ-comp iso))) ,
                (map-al (str ν))))
              (λ (ν , iso) → idp)
              λ ((f , H) , (map-comp' , c) , al) → idp

    natiso2G-ind : ∀ {k} (P : (ν : CohGrpHom {{η₁}} {{η₂}}) → WkMagNatIso-forg μ ν → Type k)
      → P μ (natiso-id2G μ)
      → {ν : CohGrpHom {{η₁}} {{η₂}}} (p : WkMagNatIso-forg μ ν) → P ν p
    natiso2G-ind P r {ν} p = ID-ind-map P natiso2G-contr r {ν} p

    natiso2G-ind-β : ∀ {k} (P : (ν : CohGrpHom {{η₁}} {{η₂}}) → WkMagNatIso-forg μ ν → Type k)
      → (r : P μ (natiso-id2G μ))
      → natiso2G-ind P r (natiso-id2G μ) == r
    natiso2G-ind-β P = ID-ind-map-β P natiso2G-contr

    natiso2G-to-== : {ν : CohGrpHom {{η₁}} {{η₂}}} → WkMagNatIso-forg μ ν → μ == ν
    natiso2G-to-== = natiso2G-ind (λ δ _ → μ == δ) idp

  natiso2G-to-==-β : (μ : CohGrpHom {{η₁}} {{η₂}}) → natiso2G-to-== (natiso-id2G μ) == idp
  natiso2G-to-==-β μ = natiso2G-ind-β (λ δ _ → μ == δ) idp  

  natiso2G-! : {μ ν : CohGrpHom {{η₁}} {{η₂}}} (iso : WkMagNatIso-forg μ ν)
    → natiso2G-to-== {μ = ν} {ν = μ} (!ʷ iso) == ! (natiso2G-to-== iso)
  natiso2G-! {μ} =
    natiso2G-ind {μ = μ}
      (λ ν iso → natiso2G-to-== {μ = ν} {ν = μ} (!ʷ iso) == ! (natiso2G-to-== iso))
    ((ap (natiso2G-to-==) (!ʷ-id (grphom-forg μ)) ∙ natiso2G-to-==-β μ) ∙
      ! (ap ! (natiso2G-to-==-β μ)))

-- iterated induction
module _ {i j k l} {G₁ : Type i} {G₂ : Type j} {G₃ : Type k} {G₄ : Type l}
  {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} {{η₃ : CohGrp G₃}}  {{η₄ : CohGrp G₄}}
  {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ : CohGrpHom {{η₃}} {{η₄}}} where

  abstract
    natiso2G-ind-bi : ∀ {ℓ}
      (P : (f₁' : CohGrpHom {{η₁}} {{η₂}}) (f₂' : CohGrpHom {{η₃}} {{η₄}}) →
        WkMagNatIso-forg f₁ f₁' → WkMagNatIso-forg f₂ f₂' → Type ℓ)
      → P f₁ f₂ (natiso-id2G f₁) (natiso-id2G f₂)
      → {f₁' : CohGrpHom {{η₁}} {{η₂}}} {f₂' : CohGrpHom {{η₃}} {{η₄}}}
        (p₁ : WkMagNatIso-forg f₁ f₁') (p₂ : WkMagNatIso-forg f₂ f₂')
        → P f₁' f₂' p₁ p₂
    natiso2G-ind-bi P r {f₁'} {f₂'} p₁ p₂ = natiso2G-ind
      (λ f ν → {f' : CohGrpHom {{η₃}} {{η₄}}} (μ : WkMagNatIso-forg f₂ f') → P f f' ν μ)
      (natiso2G-ind
        (λ (f' : CohGrpHom) (μ : WkMagNatIso-forg f₂ f') →
          P (cohgrphom (λ z → map f₁ z)) f' (natiso-id2G f₁) μ)
        r)
      {f₁'} p₁ {f₂'} p₂

-- conversion of CohGrpHom to Σ-type
module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  CohGrpHom-Σ :
    [ map ∈ (G₁ → G₂) ] ×
      [ map-comp ∈ ((x y : G₁) → mu (map x) (map y) == map (mu x y)) ] ×
        ((x y z : G₁) →
          ! (al (map x) (map y) (map z)) ∙
          ap (mu (map x)) (map-comp y z) ∙
          map-comp x (mu y z)
            ==
          ap (λ v → mu v (map z)) (map-comp x y) ∙
          map-comp (mu x y) z ∙
          ! (ap map (al x y z)))
      ≃
    CohGrpHom {{η₁}} {{η₂}}
  CohGrpHom-Σ =
   equiv
     (λ (map , map-comp , map-al) → cohgrphom map {{cohmaghomstr map-comp map-al}})
     (λ (cohgrphom map {{cohmaghomstr map-comp map-al}}) → map , (map-comp , map-al))
     (λ (cohgrphom map {{cohmaghomstr map-comp map-al}}) → idp)
     λ (map , map-comp , map-al) → idp

  CohGrpHom-1trunc : has-level 1 (CohGrpHom {{η₁}} {{η₂}})
  CohGrpHom-1trunc = equiv-preserves-level CohGrpHom-Σ

module _ {i j} {G₁ : Type i} {G₂ : Type j} {{η₁ : CohGrp G₁}} {{η₂ : CohGrp G₂}} where

  natiso2G-to-==-∙ : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₃ : CohGrpHom {{η₁}} {{η₂}}}
    (iso₂ : WkMagNatIso-forg f₁ f₂) (iso₁ : WkMagNatIso-forg f₁ f₃) (iso₃ : WkMagNatIso-forg f₂ f₃) 
    → ∼WkMagNatIso iso₁ (iso₃ natiso-∘ iso₂)
    → natiso2G-to-== {μ = f₁} {ν = f₃} iso₁ == natiso2G-to-== {ν = f₂} iso₂ ∙ natiso2G-to-== iso₃
  natiso2G-to-==-∙ {f₁} {f₂} =
    natiso2G-ind-bi {f₂ = f₁}
      (λ f₂' f₃' iso₂ iso₁ →
        (iso₃ : WkMagNatIso-forg f₂' f₃') → ∼WkMagNatIso iso₁ (iso₃ natiso-∘ iso₂)
          → natiso2G-to-== {μ = f₁} {ν = f₃'} iso₁ == natiso2G-to-== {ν = f₂'} iso₂ ∙ natiso2G-to-== iso₃)
      (λ iso₃ e → aux {iso = iso₃} (natiso∼-to-== e))
      {f₂}
      where
        aux : {iso : WkMagNatIso-forg f₁ f₁} (p : natiso-id2G f₁ == iso) →
          natiso2G-to-== (natiso-id2G f₁) == natiso2G-to-== (natiso-id2G f₁) ∙ natiso2G-to-== iso
        aux idp = ! (ap (λ p → p ∙ natiso2G-to-== (natiso-id2G f₁)) (natiso2G-to-==-β f₁))

  natiso2G-to-==-! : {f : CohGrpHom {{η₁}} {{η₂}}}
    (iso₁ iso₂ : WkMagNatIso-forg f f) → ∼WkMagNatIso iso₁ (!ʷ iso₂)
    → natiso2G-to-== {μ = f} {ν = f} iso₁ == ! (natiso2G-to-== iso₂)
  natiso2G-to-==-! {f} iso₁ iso₂ e =
    natiso2G-to-== {μ = f} {ν = f} iso₁
      =⟨ ap (natiso2G-to-==) (natiso∼-to-== {ι = iso₁} {ρ = !ʷ iso₂} e) ⟩
    natiso2G-to-== {μ = f} {ν = f} (!ʷ iso₂)
      =⟨ natiso2G-! iso₂ ⟩
    ! (natiso2G-to-== iso₂) =∎

  module _ {k} {G₃ : Type k} {{η₃ : CohGrp G₃}} where

    natiso2G-to-==-whisk-r : {f₁ : CohGrpHom {{η₁}} {{η₂}}} {f₂ f₂' : CohGrpHom {{η₂}} {{η₃}}}
      (iso₂ : WkMagNatIso-forg f₂ f₂') (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂' ∘2G f₁)) →
      ∼WkMagNatIso iso₁ (natiso-whisk-r iso₂)
      → natiso2G-to-== iso₁ == ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₂} {ν = f₂'} iso₂)
    natiso2G-to-==-whisk-r {f₁} {f₂} = 
      natiso2G-ind
        (λ f₂' iso₂ → 
          (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂' ∘2G f₁)) →
          ∼WkMagNatIso iso₁ (natiso-whisk-r iso₂)
          → natiso2G-to-== iso₁ == ap (λ m → m ∘2G f₁) (natiso2G-to-== {μ = f₂} {ν = f₂'} iso₂))
        λ iso₁ e → 
          natiso2G-to-== iso₁
            =⟨ ap natiso2G-to-== (natiso∼-to-== e) ⟩
          natiso2G-to-== (natiso-id2G (f₂ ∘2G f₁))
            =⟨ natiso2G-to-==-β (f₂ ∘2G f₁) ⟩
          idp
            =⟨ ap (ap (λ m → m ∘2G f₁)) (! (natiso2G-to-==-β f₂)) ⟩
          ap (λ m → m ∘2G f₁) (natiso2G-to-== (natiso-id2G f₂)) =∎

    natiso2G-to-==-whisk-l : {f₂ : CohGrpHom {{η₂}} {{η₃}}} {f₁ f₁' : CohGrpHom {{η₁}} {{η₂}}}
      (iso₂ : WkMagNatIso-forg f₁ f₁') (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂ ∘2G f₁')) →
      ∼WkMagNatIso iso₁ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)
      → natiso2G-to-== iso₁ == ap (λ m → f₂ ∘2G m) (natiso2G-to-== {μ = f₁} {ν = f₁'} iso₂)
    natiso2G-to-==-whisk-l {f₂} {f₁} = 
      natiso2G-ind
        (λ f₁' iso₂ → 
          (iso₁ : WkMagNatIso-forg (f₂ ∘2G f₁) (f₂ ∘2G f₁')) →
          ∼WkMagNatIso iso₁ (natiso-whisk-l {μ = grphom-forg f₂} iso₂)
          → natiso2G-to-== iso₁ == ap (λ m → f₂ ∘2G m) (natiso2G-to-== {μ = f₁} {ν = f₁'} iso₂))
        λ iso₁ e → 
          natiso2G-to-== iso₁
            =⟨ ap natiso2G-to-== (natiso∼-to-== e) ⟩
          natiso2G-to-== (natiso-id2G (f₂ ∘2G f₁))
            =⟨ natiso2G-to-==-β (f₂ ∘2G f₁) ⟩
          idp
            =⟨ ap (ap (λ m → f₂ ∘2G m)) (! (natiso2G-to-==-β f₁)) ⟩
          ap (λ m → f₂ ∘2G m) (natiso2G-to-== (natiso-id2G f₁)) =∎
