{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import lib.Basics
open import lib.FTID
open import lib.types.Sigma
open import lib.Equivalence2
open import lib.NType2
open import 2Magma
open import 2Grp
open import 2GrpProps

module 2GrpAutoEq where

open CohGrp {{...}}
open WkMag {{...}} renaming (mu to muM; al to alM)

module _ {i} {G : Type i} {{η : CohGrp G}} where
  
  open WkMagHomStr

  mu-≃-map-str : WkMagHomStr {{mag η}} {{≃-2Mag G}} (λ x → ((λ z → mu z x) , mu-post-iso x))
  map-comp (mu-≃-map-str) x y = pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓
  map-al (mu-≃-map-str) x y z =
    Subtype==-out (subtypeprop is-equiv) (post-rotate'-out mu-≃-map-aux)
    where
      mu-≃-map-aux :
        fst=
          (! (alM ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y) ((λ v → mu v z) , mu-post-iso z)) ∙
            ap (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z))) prop-has-all-paths-↓) ∙
            pair= (λ= (λ v → ! (al v x (muM y z)))) prop-has-all-paths-↓) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) prop-has-all-paths-↓) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) prop-has-all-paths-↓ ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ
        []
      mu-≃-map-aux =
        fst=
          (! (alM ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y) ((λ v → mu v z) , mu-post-iso z)) ∙
            ap (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z)))
              (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ⟨ 0 & 1 &
            ap-seq-∙ fst
              (! (alM ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y) ((λ v → mu v z) , mu-post-iso z)) ◃∙
              ap (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z)))
                (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
              pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}}) ◃∎) ⟩
        fst= (! (alM ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y)
          ((λ v → mu v z) , mu-post-iso z))) ◃∙
        fst= (ap (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z)))
          (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∙
        fst= (pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z)) (pair= (λ= (λ v → ! (al v x y)))
              (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 0 & 1 &
            ap-! fst (alM ((λ v → mu v x) , mu-post-iso x) ((λ v → mu v y) , mu-post-iso y)
              ((λ v → mu v z) , mu-post-iso z)) ∙
            ap ! (fst=-β idp _) ⟩
        idp ◃∙
        fst= (ap (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z)))
          (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∙
        fst= (pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z)) (pair= (λ= (λ v → ! (al v x y)))
              (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 1 & 1 &
            ∘-ap fst (muM ((λ v → mu v x) , mu-post-iso x)) (pair= (λ= (λ v → ! (al v y z)))
              (prop-has-all-paths-↓ {{is-equiv-level}})) ⟩
        idp ◃∙
        ap (λ f → (λ z → fst f (mu z x))) (pair= (λ= (λ v → ! (al v y z)))
          (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        fst= (pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 1 & 1 & ap-∘ (λ k → (λ z → k (mu z x))) fst (pair= (λ= (λ v → ! (al v y z)))
            (prop-has-all-paths-↓ {{is-equiv-level}})) ⟩
        idp ◃∙
        ap (λ k → (λ z → k (mu z x))) (ap fst (pair= (λ= (λ v → ! (al v y z)))
          (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∙
        fst= (pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 1 & 1 & ap (ap (λ k → (λ z → k (mu z x)))) (fst=-β (λ= (λ v → ! (al v y z)))  _) ⟩
        idp ◃∙
        ap (λ k → (λ z → k (mu z x))) (λ= (λ v → ! (al v y z))) ◃∙
        fst= (pair= (λ= (λ v → ! (al v x (muM y z)))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 2 & 1 & fst=-β (λ= (λ v → ! (al v x (muM y z)))) _ ⟩
        idp ◃∙
        ap (λ k → (λ z → k (mu z x))) (λ= (λ v → ! (al v y z))) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ₁⟨ 1 & 1 & pre∘-λ= (λ v → mu v x) (λ v → ! (al v y z)) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ! (fst=
            (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
              (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ∙
            pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ∙
            ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∎
          =ₛ⟨ 3 & 1 & 
            !-=ₛ (ap-seq-∙ fst
              (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
                (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})) ◃∙
              pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}) ◃∙
              ! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)) ◃∎)) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ! (ap fst (! (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)))) ◃∙
        ! (ap fst (pair= (λ= (λ v → ! (al v (muM x y) z))) (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∙
        ! (ap fst (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
          (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})))) ◃∎
          =ₛ₁⟨ 3 & 1 &
            !-!-ap fst (ap (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z)) ∙
            ∘-ap fst (λ x → ((λ v → mu v x) , mu-post-iso x)) (alM x y z) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        ! (ap fst (pair= (λ= (λ v → ! (al v (muM x y) z)))
          (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∙
        ! (ap fst (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
          (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})))) ◃∎
          =ₛ₁⟨ 4 & 1 & ap ! (fst=-β (λ= (λ v → ! (al v (muM x y) z))) _) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        ! (λ= (λ v → ! (al v (muM x y) z))) ◃∙
        ! (ap fst (ap (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
          (pair= (λ= (λ v → ! (al v x y))) (prop-has-all-paths-↓ {{is-equiv-level}})))) ◃∎
          =ₛ₁⟨ 5 & 1 &
            ap ! (
              ∘-ap fst (λ v → muM v ((λ v → mu v z) , mu-post-iso z))
                (pair= (λ= (λ v → ! (al v x y)))
                  (prop-has-all-paths-↓ {{is-equiv-level}}))) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        ! (λ= (λ v → ! (al v (muM x y) z))) ◃∙
        ! (ap (λ f → λ v → mu {{η}} (fst f v) z) (pair= (λ= (λ v → ! (al v x y)))
          (prop-has-all-paths-↓ {{is-equiv-level}}))) ◃∎
          =ₛ₁⟨ 5 & 1 &
            ap ! (ap-∘ (λ k → λ v → mu (k v) z) fst (pair= (λ= (λ v → ! (al v x y)))
              (prop-has-all-paths-↓ {{is-equiv-level}}))) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        ! (λ= (λ v → ! (al v (muM x y) z))) ◃∙
        ! (ap (λ k → λ v → mu (k v) z)
            (ap fst (pair= (λ= (λ v → ! (al v x y)))
              (prop-has-all-paths-↓ {{is-equiv-level}})))) ◃∎
          =ₛ₁⟨ 5 & 1 & ap ! (ap (ap (λ k → λ v → mu (k v) z)) (fst=-β (λ= (λ v → ! (al v x y))) _)) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        ! (λ= (λ v → ! (al v (muM x y) z))) ◃∙
        ! (ap (λ k → λ v → mu (k v) z) (λ= (λ v → ! (al v x y)))) ◃∎
          =ₛ₁⟨ 4 & 1 &
            λ=-! (λ v → ! (al v (muM x y) z)) ∙
            ap λ= (λ= (λ v → !-! (al v (muM x y) z))) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        λ= (λ v → al v (muM x y) z) ◃∙
        ! (ap (λ k → λ v → mu (k v) z) (λ= (λ v → ! (al v x y)))) ◃∎
          =ₛ₁⟨ 5 & 1 & ap ! (post∘-λ= (λ v → mu v z) (λ v → ! (al v x y))) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        λ= (λ v → al v (muM x y) z) ◃∙
        ! (λ= (λ v → ap (λ v → mu v z) (! (al v x y)))) ◃∎
          =ₛ₁⟨ 5 & 1 & 
            λ=-! (λ v → ap (λ v → mu v z) (! (al v x y))) ∙
            ap λ= (λ= (λ v → !-!-ap (λ v → mu v z) (al v x y))) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        ap (λ x z → mu z x) (alM x y z) ◃∙
        λ= (λ v → al v (muM x y) z) ◃∙
        λ= (λ v → ap (λ v → mu v z) (al v x y)) ◃∎
          =ₛ₁⟨ 3 & 1 & ap-λ=-curr (alM x y z) ⟩
        idp ◃∙
        λ= (λ v → ! (al (mu v x) y z)) ◃∙
        λ= (λ v → ! (al v x (muM y z))) ◃∙
        λ= (λ v → ap (mu v) (alM x y z)) ◃∙
        λ= (λ v → al v (muM x y) z) ◃∙
        λ= (λ v → ap (λ u → mu u z) (al v x y)) ◃∎
          =ₛ⟨ 1 & 5 &
            ∙5-λ=
              (λ v → ! (al (mu v x) y z))
              (λ v → ! (al v x (muM y z)))
              (λ v → ap (mu v) (alM x y z))
              (λ v → al v (muM x y) z)
              (λ v → ap (λ u → mu u z) (al v x y)) ⟩
        idp ◃∙
        λ= (λ v →
          ! (al (mu v x) y z) ∙
          ! (al v x (mu y z)) ∙
          ap (mu v) (al x y z) ∙
          al v (mu x y) z ∙
          ap (λ u → mu u z) (al v x y)) ◃∎
          =ₛ₁⟨ ap λ= (λ= λ v → ! (=ₛ-out (pent-rot2 v x y z))) ⟩
        λ= (λ v → idp) ◃∎
          =ₛ⟨ =ₛ-in (! (λ=-η idp)) ⟩
        [] ∎ₛ

module _ {i} {G : Type i} {{η : CohGrp G}} where

  open WkMagHom

  mu-≃-map : WkMagHom {{mag η}} {{≃-2Mag G}}
  fst (map mu-≃-map x) = λ z → mu z x
  snd (map mu-≃-map x) = mu-post-iso x
  str mu-≃-map = mu-≃-map-str
