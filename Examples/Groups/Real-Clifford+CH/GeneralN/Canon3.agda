------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical box facts of BoxFrames on three wires
--
-- On three wires the box is CZ on its two controls (Λ□ 2 = CZ ↑), so
-- every fact is about CZ: an involution, X on the idle wire 0 passes,
-- the swap of the controls passes (the rule comm-CZ-Ex), merging with
-- the version negated on wire 1 leaves Z on wire 2 (one two-wire
-- evaluation), that does not see the swap of the wires 0 1, and the CZ
-- of the wires 1 2 commutes with the one of the wires 0 2
-- (ThreeQubit.Auxiliary's `CZ↑-CZ₂₀`).  Only completeness on two
-- qubits is used.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon3
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; CZ² ; Ex-CZ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (φ ; net)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (by-sem₀)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (CZ↑-CZ₂₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)

open Tools (3 VRel,_===_)

private
  swaps-gen : (g : S.Gen 2) → φ g ↑ • CZ ↑ ≈ CZ ↑ • φ g ↑
  swaps-gen (S.gate₀ ())
  swaps-gen (S.gate₁ ())
  swaps-gen (S.gate₂ S.σ-gate)      = lemma-cong↑ (Ex • CZ) (CZ • Ex) Ex-CZ
  swaps-gen (S.gate₀ () S.↥)
  swaps-gen (S.gate₁ () S.↥)
  swaps-gen ((S.gate₀ () S.↥) S.↥)

  swaps-net : (w : Word (S.Gen 2)) → net w ↑ • CZ ↑ ≈ CZ ↑ • net w ↑
  swaps-net [ g ]ʷ  = swaps-gen g
  swaps-net ε       = trans left-unit (sym right-unit)
  swaps-net (u • v) = begin
    (net u ↑ • net v ↑) • CZ ↑     ≈⟨ assoc ⟩
    net u ↑ • (net v ↑ • CZ ↑)     ≈⟨ back _ (swaps-net v) ⟩
    net u ↑ • (CZ ↑ • net v ↑)     ≈⟨ sym assoc ⟩
    (net u ↑ • CZ ↑) • net v ↑     ≈⟨ front _ (swaps-net u) ⟩
    (CZ ↑ • net u ↑) • net v ↑     ≈⟨ assoc ⟩
    CZ ↑ • (net u ↑ • net v ↑) ∎

  -- CZ merged with its version negated on its control is Z on the other
  -- wire.
  merge₂ : 2 ⊢ CZ • (X • CZ • X) ≈ Z ↑
  merge₂ = by-sem₀ (CZ • (X • CZ • X)) (Z ↑) Eq.refl

  wire : Ex • Z ↑ ↑ • Ex ≈ Z ↑ ↑
  wire = trans (sym assoc) (trans (front _ (low-comm Ex Z)) (cancelʳ _ Ex²))

canon3 : Canon 0
canon3 = record
  { invol   = lemma-cong↑ (CZ • CZ) ε CZ²
  ; x-box   = X-↑ CZ
  ; swaps   = swaps-net
  ; merge   = lemma-cong↑ (CZ • (X • CZ • X)) (Z ↑) merge₂
  ; wire274 = wire
  ; comm336 = CZ↑-CZ₂₀
  }

------------------------------------------------------------------------
-- (309) on either control, the negated box first

merge3 : ∀ c → 1 ≤ c → c ≤ 2 → (Xat c • Λ□ 2 • Xat c) • Λ□ 2 ≈ placeAt c (Λ□ 1)
merge3 zero          () _
merge3 (suc zero)    _  _ = begin
  (X ↑ • CZ ↑ • X ↑) • CZ ↑                   ≈⟨ lemma-cong↑ ((X • CZ • X) • CZ) (Z ↑) m₁ ⟩
  Z ↑ ↑                                       ≈⟨ sym wire ⟩
  Ex • Z ↑ ↑ • Ex                             ≈⟨ sym (cong left-unit (back _ right-unit)) ⟩
  (ε • Ex) • Z ↑ ↑ • (Ex • ε) ∎
  where
  m₁ : 2 ⊢ (X • CZ • X) • CZ ≈ Z ↑
  m₁ = by-sem₀ ((X • CZ • X) • CZ) (Z ↑) Eq.refl
merge3 (suc (suc zero)) _ _ = begin
  (X ↑ ↑ • CZ ↑ • X ↑ ↑) • CZ ↑               ≈⟨ lemma-cong↑ ((X ↑ • CZ • X ↑) • CZ) Z m₂ ⟩
  Z ↑                                         ≈⟨ sym (lemma-cong↑ (Ex • Z ↑ • Ex) Z s₂) ⟩
  Ex ↑ • Z ↑ ↑ • Ex ↑                         ≈⟨ back _ (front _ (sym wire)) ⟩
  Ex ↑ • (Ex • Z ↑ ↑ • Ex) • Ex ↑             ≈⟨ sym (by-passoc′) ⟩
  ((ε • Ex) ↑ • Ex) • Z ↑ ↑ • (Ex • (Ex • ε) ↑) ∎
  where
  m₂ : 2 ⊢ (X ↑ • CZ • X ↑) • CZ ≈ Z
  m₂ = by-sem₀ ((X ↑ • CZ • X ↑) • CZ) Z Eq.refl
  s₂ : 2 ⊢ Ex • Z ↑ • Ex ≈ Z
  s₂ = by-sem₀ (Ex • Z ↑ • Ex) Z Eq.refl
  by-passoc′ : ((ε • Ex) ↑ • Ex) • Z ↑ ↑ • (Ex • (Ex • ε) ↑) ≈ Ex ↑ • (Ex • Z ↑ ↑ • Ex) • Ex ↑
  by-passoc′ = trans (cong (front _ left-unit) (back _ (back _ right-unit)))
                     (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)
merge3 (suc (suc (suc c))) _ (s≤s (s≤s ()))
