{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import HoTT
open import lib.wild-cats.WildCats
open import lib.types.Pointed-seq
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane
open import homotopy.SuspAdjointLoop
open import homotopy.EM-gen-rec

-- type equivalence between set-level groups and pointed n-connected, (n+1)-types

module homotopy.EM-Grp-equiv {i} (G : AbGroup i) where

open AbGroup G
open EMExplicit G
open HSpace

open ⊙EM-β G

abstract
  ⊙EM-elim₂-β-deloop : (n : ℕ) {X : Ptd i} {{X-level : has-level ⟨ S (S n) ⟩ (de⊙ X)}} (φ : grp →ᴳ Ω^'S-group (S n) X)
    → GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold (S n)) ⊙◃∎ ⊙=ₛ ⊙Ω^'-fmap (S n) (⊙EM-elimₙ G n φ) ⊙◃∎
  ⊙EM-elim₂-β-deloop O φ =
    GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
      ⊙=ₑ⟨ 0 & 1 & (⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙emloop ⊙◃∎) % ⊙=ₛ-in (! (EM₁Level₁Rec.⊙β-tri idp φ)) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙emloop ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
      ⊙=ₛ⟨ 2 & 1 & ⊙=ₛ-in idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙emloop ⊙◃∙ ⊙–> (GroupIso.⊙f-equiv (Ω¹-EM₁ grp)) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ₁⟨ 1 & 2 & ⊙λ= ((<–-inv-r (emloop-equiv grp)) , prop-has-all-paths-↓ {{has-level-apply-instance {{has-level-apply-instance {{EM₁-level₁ grp}}}}}}) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙idf (⊙Ω (⊙EM₁ grp)) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ₁⟨ 0 & 2 & idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
      ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in idp ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙
    ⊙–> (⊙unTrunc-equiv (⊙Ω (⊙EM₁ grp)) {{has-level-apply-instance {{EM₁-level₁ grp}}}}) ⊙◃∙
    ⊙Ω-Trunc-[_] (⊙EM₁ grp) ⊙◃∎
      ⊙=ₛ⟨ 1 & 2 & ⊙=ₛ-in (⊙-comp-to-== (=ₜ-equiv-ind {n = 0}
        {P = λ (p : [ embase' (fst G) ] == [ embase' (fst G) ]) →
          Trunc-elim {{has-level-apply-instance {{EM₁-level₁ grp}}}} (λ v → v)
            (=ₜ-maps.to [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ] p)
            ==
          ap (Trunc-elim {P = λ _ → EM₁ grp} {{EM₁-level₁ grp}} (λ v → v)) p}
         (Trunc-elim {P = λ p →
           Trunc-elim {{has-level-apply-instance {{EM₁-level₁ grp}}}} (λ v → v)
             (=ₜ-maps.to [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ] (Trunc-elim (ap [_]) p))
             ==
           ap (Trunc-elim {P = λ _ → EM₁ grp} {{EM₁-level₁ grp}} (λ v → v))
             (Trunc-elim {P = λ _ → [ embase' grp ] == [ embase' grp ]} (ap [_]) p)} lemma) ,
       idp)) ⟩
    ⊙Ω-fmap (EM₁-level₁-rec idp φ , idp) ⊙◃∙
    ⊙Ω-fmap (⊙–> (⊙unTrunc-equiv (⊙EM₁ grp) {{EM₁-level₁ grp}})) ⊙◃∎
      ⊙=ₛ₁⟨ ! (⊙Ω-fmap-∘ (EM₁-level₁-rec idp φ , idp) (⊙–> (⊙unTrunc-equiv (⊙EM₁ grp) {{EM₁-level₁ grp}}))) ⟩
    ⊙Ω-fmap ((EM₁-level₁-rec idp φ ∘ –> (unTrunc-equiv (EM₁ grp) {{EM₁-level₁ grp}})) , idp) ⊙◃∎ ⊙∎ₛ
      where
        lemma : {c : EM₁ grp} (p : embase' grp == c) →
          Trunc-elim {{has-level-apply-instance {{EM₁-level₁ grp {n = ⟨-2⟩}}}}} (λ v → v) (=ₜ-maps.to [ embase' grp ] [ c ] _ _ (ap [_] p))
            ==
          ap (Trunc-elim {P = λ _ → EM₁ grp} {{EM₁-level₁ grp {n = ⟨-2⟩}}} (λ v → v)) (ap [_] p)
        lemma idp = idp
  ⊙EM-elim₂-β-deloop (S n) φ = 
    GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold (S (S n))) ⊙◃∎
      ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in idp ⟩
    GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold (S n)) ⊙◃∙ ⊙–> (⊙Ω^'-emap (S n) (spectrum (S n))) ⊙◃∎
      ⊙=ₛ⟨ 0 & 2 & ⊙EM-elim₂-β-deloop n φ ⟩
    ⊙Ω^'-fmap (S n) (⊙EM-elimₙ G n φ) ⊙◃∙ ⊙–> (⊙Ω^'-emap (S n) (spectrum (S n))) ⊙◃∎
      ⊙=ₛ₁⟨ ! (⊙Ω^'-fmap-∘ (S n) (⊙EM-elimₙ G n φ) (⊙–> (spectrum (S n)))) ⟩
    ⊙Ω^'-fmap (S n) (⊙EM-elimₙ G n φ ⊙∘ ⊙–> (spectrum (S n))) ⊙◃∎
      ⊙=ₛ₁⟨ ap (⊙Ω^'-fmap (S n)) (! (⊙EM-elim₂-β-rot n φ)) ⟩
    ⊙Ω^'-fmap (S n) (⊙Ω-fmap (⊙EM-elimₙ G (S n) φ)) ⊙◃∎ ⊙∎ₛ
