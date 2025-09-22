{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 --lossy-unification #-}

open import HoTT
open import lib.wild-cats.WildCats
open import lib.types.Pointed-seq
open import homotopy.Freudenthal
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane
open import homotopy.SuspAdjointLoop

-- general recursion principle for K(G, n)

module homotopy.EM-gen-rec {i} (G : AbGroup i) where

open AbGroup G
open EMExplicit G

⊙EM-elimₙ : (n : ℕ) {j : ULevel} {X : Ptd j} {{X-level : has-level ⟨ S n ⟩ (de⊙ X)}}
  → (grp →ᴳ Ω^'S-group n X) → ⊙EM (S n) ⊙→ X
⊙EM-elimₙ O {X = X@(⊙[ X₀ , pt ])} φ = (f ∘ –> (unTrunc-equiv (EM₁ (fst G)) {{EM₁-level₁ grp}})) , idp
  where open EM₁Level₁Rec pt φ
⊙EM-elimₙ (S n) {X = X} φ =
  ⊙Trunc-rec (ε X ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ [_]-⊙))

open HSpace

{-
-- Lossy unification makes these three equalities feasible for Agda:

_ : spectrum 1 == Pi2HSusp.⊙eq {{EM₁-level₁ grp}} H-⊙EM₁ ⊙∘e ⊙Ω-Trunc-[ ⊙Susp (⊙EM₁ grp) ]-≃
_ = idp

test : (n : ℕ) → Spectrum.spectrumSS n == Spectrum.FS.⊙eq n {{⊙Susp^-conn' (S n)}} ⊙⁻¹ ⊙∘e ⊙Ω-Trunc-[_]-≃ (⊙Susp^ (S (S n)) (⊙EM₁ grp))
test n = idp

_ : ⊙<– (Pi2HSusp.⊙eq {{EM₁-level₁ grp}} H-⊙EM₁) == ⊙Trunc-fmap (η (⊙EM₁ grp))
_ = Pi2HSusp.⊙eq-inv-rew {{EM₁-level₁ grp}} H-⊙EM₁
-}

abstract
  ⊙<–-spectrumS : (n : ℕ) → ⊙<– (spectrum (S n)) ⊙◃∎ ⊙=ₛ ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
  ⊙<–-spectrumS O =
    ⊙<– (Pi2HSusp.⊙eq {{EM₁-level₁ grp}} H-⊙EM₁ ⊙∘e ⊙Ω-Trunc-[_]-≃ (⊙Susp (⊙EM₁ grp))) ⊙◃∎
      ⊙=ₛ⟨ ⊙=ₛ-in (⊙<–-∘ (⊙Ω-Trunc-[_]-≃  (⊙Susp (⊙EM₁ grp))) (Pi2HSusp.⊙eq {{EM₁-level₁ grp}} H-⊙EM₁)) ⟩
    ⊙Ω-UnTrunc-[_] (⊙Susp (⊙EM₁ grp)) ⊙◃∙ ⊙<– (Pi2HSusp.⊙eq {{EM₁-level₁ grp}} H-⊙EM₁) ⊙◃∎
      ⊙=ₛ₁⟨ 1 & 1 & Pi2HSusp.⊙eq-inv-rew {{EM₁-level₁ grp}} H-⊙EM₁ ⟩
    ⊙Ω-UnTrunc-[_] (⊙Susp (⊙EM₁ grp)) ⊙◃∙ ⊙Trunc-fmap (η (⊙EM₁ grp)) ⊙◃∎ ⊙∎ₛ
  ⊙<–-spectrumS (S n) =
    ⊙<– (Spectrum.FS.⊙eq n {{⊙Susp^-conn' (S n)}} ⊙⁻¹ ⊙∘e ⊙Ω-Trunc-[_]-≃ (⊙Susp^ (S (S n)) (⊙EM₁ grp))) ⊙◃∎
      ⊙=ₛ⟨ ⊙=ₛ-in (⊙<–-∘ (⊙Ω-Trunc-[_]-≃  (⊙Susp^ (S (S n)) (⊙EM₁ grp))) (Spectrum.FS.⊙eq n {{⊙Susp^-conn' (S n)}} ⊙⁻¹)) ⟩
    ⊙Ω-UnTrunc-[_] (⊙Susp^ (S (S n)) (⊙EM₁ grp)) ⊙◃∙ ⊙<– (Spectrum.FS.⊙eq n {{⊙Susp^-conn' (S n)}} ⊙⁻¹) ⊙◃∎
      ⊙=ₛ₁⟨ 1 & 1 & ⊙<–-invl (Spectrum.FS.⊙eq n {{⊙Susp^-conn' (S n)}}) ⟩
    ⊙Ω-UnTrunc-[ ⊙Susp (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ] ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ (S n) (⊙EM₁ grp))) ⊙◃∎ ⊙∎ₛ

module ⊙EM-β (n : ℕ) {X : Ptd i} {{X-level : has-level ⟨ S (S n) ⟩ (de⊙ X)}}
  (φ : grp →ᴳ Ω^'S-group (S n) X) where

  abstract
    ⊙EM-elimₙ-β : ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙<– (spectrum (S n)) ⊙◃∎ ⊙=ₛ ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙◃∎
    ⊙EM-elimₙ-β = let τ = ε X ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ [_]-⊙) in
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙<– (spectrum (S n)) ⊙◃∎
        ⊙=ₛ⟨ 1 & 1 & ⊙<–-spectrumS n ⟩
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙◃∙ ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ₁⟨ 0 & 1 & idp ⟩
      ⊙Ω-fmap (⊙Trunc-rec τ) ⊙◃∙ ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙ ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₑ⟨ 0 & 1 & (⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
                     ⊙Trunc-fmap (⊙Ω-fmap (ε X ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∙
                     ⊙Ω-Trunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎)
          % ⊙=ₛ-in (! (⊙Ω-Trunc-rec-coh τ)) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X ⊙∘ ⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∙
      ⊙Ω-Trunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₑ⟨ 1 & 1 & (⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙ ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∎)
          % ⊙=ₛ-in $
             ap ⊙Trunc-fmap (⊙Ω-fmap-∘ (ε X) (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ∙
             ! (⊙Trunc-fmap-∘ (⊙Ω-fmap (ε X)) (⊙Ω-fmap (⊙Susp-fmap (⊙EM-elimₙ n φ ⊙∘ [_]-⊙)))) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∙
      ⊙Ω-Trunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Ω-UnTrunc-[_] (⊙Susp (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ₁⟨ 3 & 2 & ⊙λ= (⊙<–-inv-r (⊙Ω-Trunc-[_]-≃ (⊙Susp (⊙Susp^ n (⊙EM₁ grp))))) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∙
      ⊙idf (⊙Trunc (S (S (S ⟨ n ⟩₋₂))) (⊙Ω (⊙Susp (⊙Susp^ n (⊙EM₁ grp))))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ₁⟨ 2 & 2 & idp ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap {X = ⊙Susp^ n (⊙EM₁ grp)} (⊙EM-elimₙ n φ ⊙∘ [_]-⊙))) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Susp^ n (⊙EM₁ grp))) ⊙◃∎
        ⊙=ₛ⟨ 2 & 2 & ⊙=ₛ-in (Nat-trans.sq (nat-trans-whisk-r Nat-trans-η ⊙Trunc-wf) (⊙EM-elimₙ n φ ⊙∘ [_]-⊙)) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙Ω-fmap (ε X)) ⊙◃∙
      ⊙Trunc-fmap (η (⊙Ω X))⊙◃∙
      ⊙Trunc-fmap (⊙EM-elimₙ n φ ⊙∘ [_]-⊙) ⊙◃∎
        ⊙=ₛ₁⟨ 1 & 2 & F-Gε-ηG ⊙Trunc-wf X ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙idf (⊙Trunc (S (S (S ⟨ n ⟩₋₂))) (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙EM-elimₙ n φ ⊙∘ [_]-⊙) ⊙◃∎
        ⊙=ₛ₁⟨ 0 & 2 & idp ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙EM-elimₙ n φ ⊙∘ [_]-⊙) ⊙◃∎
        ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in (! (⊙Trunc-fmap-∘ (⊙EM-elimₙ n φ) [_]-⊙)) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙EM-elimₙ n φ) ⊙◃∙
      ⊙Trunc-fmap [_]-⊙ ⊙◃∎
        ⊙=ₛ₁⟨ 2 & 1 & ⊙-comp-to-== ((Trunc-elim (λ _ → idp)) , idp) ⟩
      ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ⊙◃∙
      ⊙Trunc-fmap (⊙EM-elimₙ n φ) ⊙◃∙
      [_]-⊙ ⊙◃∎
        ⊙=ₛ₁⟨ ! (⊙-unTrunc-fmap-nat-rot-in (⊙EM-elimₙ n {X = ⊙Ω X} φ)) ⟩
      ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙◃∎ ⊙∎ₛ
      
  abstract
    ⊙EM-elim₂-β-rot : ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) == ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ ⊙–> (spectrum (S n))
    ⊙EM-elim₂-β-rot = 
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ)
        =⟨ ap (λ m → ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ m) (! (⊙λ= (⊙<–-inv-l (spectrum (S n))))) ⟩
      ⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ ⊙<– (spectrum (S n)) ⊙∘ ⊙–> (spectrum (S n))
        =⟨ ! (⊙λ= (⊙∘-assoc (⊙Ω-fmap (⊙EM-elimₙ (S n) φ)) (⊙<– (spectrum (S n))) (⊙–> (spectrum (S n))))) ⟩
      (⊙Ω-fmap (⊙EM-elimₙ (S n) φ) ⊙∘ ⊙<– (spectrum (S n))) ⊙∘ ⊙–> (spectrum (S n))
        =⟨ ap (λ m → m ⊙∘ ⊙–> (spectrum (S n))) (⊙=ₛ-out ⊙EM-elimₙ-β) ⟩
      ⊙EM-elimₙ n {X = ⊙Ω X} φ ⊙∘ ⊙–> (spectrum (S n)) =∎
