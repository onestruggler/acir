------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (44) of Figure 8 (Clément, Appendix E.5)
--
-- (44) is X_[0,3] X_[1,2] · H_[0,1] H_[3,2] = H_[0,1] H_[3,2] · X_[0,3] X_[1,2].
-- Decoded, H_[0,1] H_[3,2] is the gadget, the H gate on wire 1 with its
-- box wire on wire 0 (Layout.gadget-form), and X_[0,3] X_[1,2] is
-- XX0312's `Cc`.  They share the negations of the wires 2 … (Layout's
-- `T`), which are conjugated away; what is left is the module's
-- parameter `core`, which GeneralN.Canon44 gives at every width from
-- five on.  The decodings are reversed, and reversal is a congruence
-- (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule44
  {m : ℕ}
  (core : (₃₊ m) ⊢ (Ex ↓ • ΛH (₁₊ m) • Ex ↓) •
                    (((Ex ↓ • ΛXZ (₂₊ m) • Ex ↓) • (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) • Λ□ (₂₊ m)) •
                     ((X ↑ • ΛXZ (₂₊ m) • X ↑) • (ΛXZ (₂₊ m) • (Ex ↓ • ΛXZ (₂₊ m) • Ex ↓) • ΛZX (₂₊ m)) •
                      (X ↑ • ΛZX (₂₊ m) • X ↑)))
                  ≈ (((Ex ↓ • ΛXZ (₂₊ m) • Ex ↓) • (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) • Λ□ (₂₊ m)) •
                     ((X ↑ • ΛXZ (₂₊ m) • X ↑) • (ΛXZ (₂₊ m) • (Ex ↓ • ΛXZ (₂₊ m) • Ex ↓) • ΛZX (₂₊ m)) •
                      (X ↑ • ΛZX (₂₊ m) • X ↑))) •
                    (Ex ↓ • ΛH (₁₊ m) • Ex ↓))
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Encoding using (xxℕ ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dXX ; gadget)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh0132)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m} using (module CT ; S ; gadget-form)
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 {m} using (Cc ; d-xx ; xx-form)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  ------------------------------------------------------------------------
  -- The unreversed rule

  unrev : gadget {m} • dXX {m} 0 3 1 2 ≈ dXX {m} 0 3 1 2 • gadget {m}
  unrev = begin
    gadget • dXX 0 3 1 2      ≈⟨ cong gadget-form xx-form ⟩
    CT.⟪ S ⟫ • CT.⟪ Cc ⟫      ≈⟨ CT.⟪⟫-≈ core (CT.⟪⟫-•₂ refl refl) (CT.⟪⟫-•₂ refl refl) ⟩
    CT.⟪ Cc ⟫ • CT.⟪ S ⟫      ≈⟨ sym (cong xx-form gadget-form) ⟩
    dXX 0 3 1 2 • gadget ∎

------------------------------------------------------------------------
-- (44)

e44 : (d ʷ) (xxℕ {N} 0 3 1 2 • hhℕ 0 1 3 2) ≈ (d ʷ) (hhℕ {N} 0 1 3 2 • xxℕ 0 3 1 2)
e44 = begin
  (d ʷ) (xxℕ 0 3 1 2 • hhℕ 0 1 3 2)     ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-xx d-hh0132) ⟩
  rev (dXX 0 3 1 2) • rev gadget         ≈⟨ rev-cong unrev ⟩
  rev gadget • rev (dXX 0 3 1 2)         ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-hh0132 d-xx)) ⟩
  (d ʷ) (hhℕ 0 1 3 2 • xxℕ 0 3 1 2) ∎
