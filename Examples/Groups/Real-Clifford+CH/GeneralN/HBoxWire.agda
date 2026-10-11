------------------------------------------------------------------------
-- Presentations of groups
--
-- The box wire of the multi-controlled H can be moved to an idle wire
-- (Clément, Lemma D.8, Equation (277))
--
-- The H gate one wire up is the box one wire up between P ⊗ P on the
-- wires 1 2.  By (276) the box also passes P ⊗ P on the wires 0 1, and
-- on the triangle 0 1 2 the three P ⊗ P form a Klein four-group, (130):
-- each side's two P ⊗ P make the third, which is P ⊗ P on the wires 1 2
-- between swaps of the wires 0 1 (one evaluation on three wires).  That
-- swap passes the box, (274), so the H gate passes it: its box wire can
-- be exchanged with the idle wire below.
--
-- (274) needs (285) one width down, and (276) needs (284) there; both
-- come from completeness one width down, their semantics being checked
-- in GeneralN.Sem.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.HBoxWire
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire complete₂ complete₃ using (eq274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PPBox complete₂ complete₃ using (eq276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (sem285)

-- (277): the H gate one wire up, its box wire exchanged with the idle
-- wire below.
Eq277 : ℕ → Set
Eq277 k = (₁₊ (₄₊ k)) ⊢ Ex ↓ • ΛH (₂₊ k) ↑ • Ex ↓ ≈ ΛH (₂₊ k) ↑

module _ (k : ℕ) (complete : ∀ {u v : Circuit (₄₊ k)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (₄₊ k) ⊢ u ≈ v) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)

    Λ↑ : Circuit (₁₊ (₄₊ k))
    Λ↑ = Λ□ (₃₊ k) ↑

    -- (274), (285) coming from completeness one width down.
    e274 : (₁₊ (₄₊ k)) ⊢ Ex ↓ • Λ↑ • Ex ↓ ≈ Λ↑
    e274 = eq274 k (complete (sem285 k))

    -- The Klein four-group on the wires 0 1 2, (130).
    klein₁ : (₁₊ (₄₊ k)) ⊢ Ex ↓ • PP ↑ • Ex ↓ ≈ PP ↑ • PP ↓
    klein₁ = L₃-sem (Ex ↓ • PP ↑ • Ex ↓) (PP ↑ • PP ↓) Eq.refl

    klein₂ : (₁₊ (₄₊ k)) ⊢ Ex ↓ • PP ↑ • Ex ↓ ≈ PP ↓ • PP ↑
    klein₂ = L₃-sem (Ex ↓ • PP ↑ • Ex ↓) (PP ↓ • PP ↑) Eq.refl

  eq277 : Eq277 k
  eq277 = begin
    Ex ↓ • (PP ↑ • Λ↑ • PP ↑) • Ex ↓
      ≈⟨ back _ (front _ (back _ (front _ (sym e274)))) ⟩
    Ex ↓ • (PP ↑ • (Ex ↓ • Λ↑ • Ex ↓) • PP ↑) • Ex ↓
      ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
    (Ex ↓ • PP ↑ • Ex ↓) • Λ↑ • (Ex ↓ • PP ↑ • Ex ↓)
      ≈⟨ cong klein₁ (back _ klein₂) ⟩
    (PP ↑ • PP ↓) • Λ↑ • (PP ↓ • PP ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    PP ↑ • (PP ↓ • Λ↑ • PP ↓) • PP ↑
      ≈⟨ back _ (front _ (eq276 k complete)) ⟩
    PP ↑ • Λ↑ • PP ↑ ∎
