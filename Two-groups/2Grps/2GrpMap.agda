{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=6 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths
open import 2Magma
open import 2Grp

module 2GrpMap where

open CohGrp {{...}}
open WkMagHomStr
open CohGrpHom
open WkMagNatIso

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
      natiso2G-contr : is-contr (Σ (CohGrpHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso (grphom-forg μ) (grphom-forg ν)))
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
            Σ (CohGrpHom {{η₁}} {{η₂}}) (λ ν → WkMagNatIso (grphom-forg μ) (grphom-forg ν))
          aux = 
            equiv
              (λ ((f , H) , (map-comp' , c) , al) → (cohgrphom f {{cohmaghomstr (curry map-comp') al}}) ,
                cohgrpnatiso H (curry c))
              (λ (ν , iso) → ((map ν) , (θ iso)) , (((uncurry (map-comp (str ν))) , (uncurry (θ-comp iso))) ,
                (map-al (str ν))))
              (λ (ν , iso) → idp)
              λ ((f , H) , (map-comp' , c) , al) → idp

    natiso2G-ind : ∀ {k} (P : (ν : CohGrpHom {{η₁}} {{η₂}}) → WkMagNatIso (grphom-forg μ) (grphom-forg ν) →  Type k)
      → P μ (natiso-id (grphom-forg μ))
      → (ν : CohGrpHom {{η₁}} {{η₂}}) (p : WkMagNatIso (grphom-forg μ) (grphom-forg ν)) → P ν p
    natiso2G-ind P r ν p = ID-ind-map P natiso2G-contr r {ν} p

    natiso2G-ind-β : ∀ {k} (P : (ν : CohGrpHom {{η₁}} {{η₂}}) → WkMagNatIso (grphom-forg μ) (grphom-forg ν) →  Type k)
      → (r : P μ (natiso-id (grphom-forg μ)))
      → natiso2G-ind P r μ (natiso-id (grphom-forg μ)) == r
    natiso2G-ind-β P = ID-ind-map-β P natiso2G-contr

    natiso2G-to-== : {ν : CohGrpHom {{η₁}} {{η₂}}} → WkMagNatIso (grphom-forg μ) (grphom-forg ν) → μ == ν
    natiso2G-to-== {ν} = natiso2G-ind (λ δ _ → μ == δ) idp ν
