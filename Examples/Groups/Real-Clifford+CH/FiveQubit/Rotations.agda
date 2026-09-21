------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P under the triply controlled rotation (Clément, Lemma D.7,
-- Equation (262))
--
-- The triply controlled ZX on the wires 1–4, its target on wire 1, is
-- a B a B with a the CH of the wires 1 2 and B the box on wire 2.
-- Between P ⊗ P on the wires 0 1 the CH becomes the CZ, the rule (18),
-- and the box — P ⊗ P sits on a control and the fifth wire — becomes the
-- doubly controlled H on wire 1: by the Klein four-group on the wires
-- 0 1 2 the two P ⊗ P that make that H gate differ from this one by the
-- one on the wires 0 2, the box wire and the fifth wire, which (250)
-- absorbs.  The result, c G c G, is the XZ in its form (213), the
-- control on wire 1 in the role of wire 3.  This is (174) one level up.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; PP₀₁² ; klein-ca ; ΛH₀₁-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₀₂ ; PP₁₂² ; PP₀₂² ; PP-triangle₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; XZ₃-form₃ ; S₁₂-XZ₃)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Auxiliary complete₂ complete₃
  using (box₃↑ ; eq250)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (PP-CH↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The XZ with the control on wire 1 in the role of wire 3

private
  XZ₃-form₁ : (₄₊ n) ⊢ XZ₃ ≈ CZ ↓ • ΛH₀₁ • CZ ↓ • ΛH₀₁
  XZ₃-form₁ {n} = S₁₂.⟪⟫-≈ XZ₃-form₃ S₁₂-XZ₃ (S₁₂.⟪⟫-•₄ c G c G)
    where
    open Tools ((₄₊ n) VRel,_===_)
    c : S₁₂.⟪ CZ₂₀ ⟫ ≈ CZ ↓
    c = trans (S₁₂.⟪⟫-cong (sym (O-L CZ))) (S₁₂.⟪⟫-⟪⟫ (CZ ↓))
    G : S₁₂.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ≈ ΛH₀₁
    G = S₁₂.⟪⟫-⟪⟫ ΛH₀₁

------------------------------------------------------------------------
-- (262)

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ

  private
    module Pj = Conj {₁₊ (₄₊ n)} PP₀₁ PP₀₁²

    B↑ : Circuit (₁₊ (₄₊ n))
    B↑ = box₃′ ↑

    -- The Klein four-group on the wires 0 1 2.
    e₁ : PP₁₂ • PP₀₁ ≈ PP₀₂
    e₁ = klein-ca Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂

    cb : PP₁₂ • PP₀₂ ≈ PP₀₁
    cb = trans (back _ (sym e₁)) (cancelˡ _ PP₁₂²)

    bc : PP₀₂ • PP₁₂ ≈ PP₀₁
    bc = trans (front _ (sym PP-triangle₂)) (cancelʳ _ PP₁₂²)

    -- (250) under the middle swap: P ⊗ P on the box wire 2 and wire 0.
    PP₀₂-B↑ : PP₀₂ • B↑ • PP₀₂ ≈ B↑
    PP₀₂-B↑ = S₁₂.⟪⟫-≈ eq250 (S₁₂.⟪⟫-•₃ (O-L PP) refl (O-L PP)) refl

    -- The box between P ⊗ P on a control and the fifth wire is the H gate.
    Pj-B↑ : Pj.⟪ B↑ ⟫ ≈ ΛH₀₁ ↑
    Pj-B↑ = begin
      PP₀₁ • B↑ • PP₀₁
        ≈⟨ cong (sym cb) (back _ (sym bc)) ⟩
      (PP₁₂ • PP₀₂) • B↑ • (PP₀₂ • PP₁₂)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      PP₁₂ • (PP₀₂ • B↑ • PP₀₂) • PP₁₂
        ≈⟨ back _ (front _ PP₀₂-B↑) ⟩
      PP₁₂ • B↑ • PP₁₂
        ≈⟨ sym (lemma-cong↑ ΛH₀₁ (PP₀₁ • box₃′ • PP₀₁) ΛH₀₁-PP) ⟩
      ΛH₀₁ ↑ ∎

    Pj-ZX : Pj.⟪ ZX₃ ↑ ⟫ ≈ XZ₃ ↑
    Pj-ZX = trans (Pj.⟪⟫-•₄ PP-CH↑ Pj-B↑ PP-CH↑ Pj-B↑)
                  (sym (lemma-cong↑ XZ₃ (CZ ↓ • ΛH₀₁ • CZ ↓ • ΛH₀₁) XZ₃-form₁))

  eq262 : PP₀₁ • ZX₃ ↑ ≈ XZ₃ ↑ • PP₀₁
  eq262 = begin
    PP₀₁ • ZX₃ ↑                    ≈⟨ sym right-unit ⟩
    (PP₀₁ • ZX₃ ↑) • ε              ≈⟨ back _ (sym PP₀₁²) ⟩
    (PP₀₁ • ZX₃ ↑) • PP₀₁ • PP₀₁    ≈⟨ by-passoc ((□ • □) • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (PP₀₁ • ZX₃ ↑ • PP₀₁) • PP₀₁    ≈⟨ front _ Pj-ZX ⟩
    XZ₃ ↑ • PP₀₁ ∎
