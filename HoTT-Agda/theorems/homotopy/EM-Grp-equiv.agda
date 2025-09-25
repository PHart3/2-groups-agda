{-# OPTIONS --without-K --rewriting --overlapping-instances --instance-search-depth=3 #-}

open import HoTT
open import lib.types.Pointed-seq
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLane1
open import homotopy.SuspAdjointLoop
open import homotopy.EM-gen-rec
open import homotopy.Loop-conn-equiv

-- type equivalence between set-level groups and pointed n-connected, (n+1)-types

module homotopy.EM-Grp-equiv where

module ⊙EM-β-deloop {i} (G : AbGroup i) where

  open AbGroup G
  open EMExplicit G
  open ⊙EM-β G

  abstract
    ⊙EM-elim₂-β-deloop : (n : ℕ) {X : Ptd i} {{X-level : has-level ⟨ S n ⟩ (de⊙ X)}} (φ : grp →ᴳ Ω^'S-group n X)
      → GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold (S n)) ⊙◃∎ ⊙=ₛ ⊙Ω^'-fmap (S n) (⊙EM-elimₙ G n φ) ⊙◃∎
    ⊙EM-elim₂-β-deloop O {X} φ =
      GroupHom.⊙f φ ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
        ⊙=ₑ⟨ 0 & 1 & (⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙ ⊙emloop ⊙◃∎) % ⊙=ₛ-in (! (EM₁Level₁Rec.⊙β-tri (pt X) φ)) ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙ ⊙emloop ⊙◃∙ ⊙–> (deloop'-fold 1) ⊙◃∎
        ⊙=ₛ⟨ 2 & 1 & ⊙=ₛ-in idp ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙
      ⊙emloop ⊙◃∙ ⊙–> (GroupIso.⊙f-equiv (Ω¹-EM₁ grp)) ⊙◃∙
      ⊙–> Spectrum.spectrum0 ⊙◃∎
        ⊙=ₛ₁⟨ 1 & 2 & ⊙λ= ((<–-inv-r (emloop-equiv grp)) , prop-has-all-paths-↓
          {{has-level-apply-instance {{has-level-apply-instance {{EM₁-level₁ grp}}}}}}) ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙ ⊙idf (⊙Ω (⊙EM₁ grp)) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
        ⊙=ₛ₁⟨ 0 & 2 & idp ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙ ⊙–> Spectrum.spectrum0 ⊙◃∎
        ⊙=ₛ⟨ 1 & 1 & ⊙=ₛ-in idp ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙
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
               (=ₜ-maps.to [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ] [ embase' (fst G) ]
                 (Trunc-elim (ap [_]) p))
               ==
             ap (Trunc-elim {P = λ _ → EM₁ grp} {{EM₁-level₁ grp}} (λ v → v))
               (Trunc-elim {P = λ _ → [ embase' grp ] == [ embase' grp ]} (ap [_]) p)} lemma) ,
         idp)) ⟩
      ⊙Ω-fmap (EM₁-level₁-rec (pt X) φ , idp) ⊙◃∙
      ⊙Ω-fmap (⊙–> (⊙unTrunc-equiv (⊙EM₁ grp) {{EM₁-level₁ grp}})) ⊙◃∎
        ⊙=ₛ₁⟨ ! (⊙Ω-fmap-∘ (EM₁-level₁-rec (pt X) φ , idp) (⊙–> (⊙unTrunc-equiv (⊙EM₁ grp) {{EM₁-level₁ grp}}))) ⟩
      ⊙Ω-fmap ((EM₁-level₁-rec (pt X) φ ∘ –> (unTrunc-equiv (EM₁ grp) {{EM₁-level₁ grp}})) , idp) ⊙◃∎ ⊙∎ₛ
        where
          lemma : {c : EM₁ grp} (p : embase' grp == c) →
            Trunc-elim {{has-level-apply-instance {{EM₁-level₁ grp {n = ⟨-2⟩}}}}} (λ v → v)
              (=ₜ-maps.to [ embase' grp ] [ c ] _ _ (ap [_] p))
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

module _ (n : ℕ) where

  open ⊙EM-β-deloop
  open EMExplicit

  groupal-grpd-Ab : (i : ULevel) → Type (lsucc i)
  groupal-grpd-Ab i = Σ (Ptd i) (λ X → has-level ⟨ S (S n) ⟩ (de⊙ X) × is-connected ⟨ S n ⟩ (de⊙ X) ) 

  private
    ext : ∀ {i} {X Y : groupal-grpd-Ab i} → fst X ⊙≃ fst Y → X == Y
    ext e = pair= (⊙≃-to-== e) prop-has-all-paths-↓

  EM-Ab-equiv : ∀ {i} → groupal-grpd-Ab i ≃ AbGroup i
  EM-Ab-equiv {i} = equiv Omega-grp EM-spce rt1 rt2
    where

      Omega-grp : groupal-grpd-Ab i → AbGroup i
      Omega-grp (X , tX , _) = Ω^'S-abgroup n X {{tX}}

      EM-spce : AbGroup i → groupal-grpd-Ab i
      EM-spce G = (⊙EM G (S (S n))) , ((EM-level G (S (S n))) , (EM-conn G))

      rt1 : (G : AbGroup i) → Omega-grp (EM-spce G) == G
      rt1 G = uaᴳ-Ab ((group-hom (fst (⊙–> (deloop'-fold G (S (S n))))) (deloop'-fold-pres-comp G (S n))) ,
        (snd (deloop'-fold G (S (S n)))))

      rt2 : (T : groupal-grpd-Ab i) → EM-spce (Omega-grp T) == T
      rt2 T@(X , tX , cX) = let
        open AbGroup (Omega-grp T) 
        τ = ⊙EM-elimₙ (Omega-grp T) (S n) {{tX}} (idhom grp) in
        ext (τ , Ω-Nconn-≃ {n = S n} {{EM-conn (Omega-grp T)}} {{cX}} τ
          (transport is-equiv (fst= (⊙=ₛ-out (⊙EM-elim₂-β-deloop (Omega-grp T) (S n) {{tX}} (idhom grp))))
            (idf-is-equiv _ ∘ise snd (deloop'-fold (Omega-grp T) (S (S n)))) ))
