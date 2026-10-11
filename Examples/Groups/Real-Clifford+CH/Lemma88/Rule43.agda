------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (43) of Figure 8 (Clément, Appendix E.5)
--
-- (43) is H_[0,1] H_[3,2] · H_[3,2] H_[4,5]
--       = X_[0,3] X_[1,2] · H_[3,2] H_[4,5] · X_[0,3] X_[1,2].
-- Decoded, H_[0,1] H_[3,2] is the gadget (Layout.gadget-form), and
-- H_[3,2] H_[4,5] (H-pattern (0 , 2)) is the H gate on wire 0 with its
-- box wire on wire 2, black on wire 1 — between the negations of the
-- wires 2 … it is the swapped H gate negated on its box wire.  The
-- decoded X_[0,3] X_[1,2] is XX0312's `Cc`.  All three share Layout's
-- negations `T`, which are conjugated away; what is left is the
-- module's parameter `core`.  The decodings are reversed, and reversal
-- is a congruence (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 using (Cc)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule43
  {m : ℕ}
  (core : (₃₊ m) ⊢ (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • X ↑ ↑) • (Ex ↓ • ΛH (₁₊ m) • Ex ↓)
                  ≈ Cc {m} • (X ↑ ↑ • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • X ↑ ↑) • Cc {m})
  where

open import Data.Bool using (true ; false)
open import Data.Maybe using (just)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _ʷ)

open import Notations using (₂ ; ₃ ; ₄ ; ₅)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Encoding using (xxℕ ; hhℕ ; hpat)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (ctrl ; tgt ; tgtH ; Layout ; negs ; conj₂ ; mcH)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dXX ; gcode ; gadget ; layoutH ; layoutHFrom)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters using (hpat-flips)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh-pat ; d-hh0132)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; g2 ; g3 ; g4 ; g5 ; negs-tail ; negs-tail₀₂ ; NY ; T ; module CT ; S ; gadget-form)
open import Examples.Groups.Real-Clifford+CH.Lemma88.XX0312 {m} using (d-xx ; xx-form)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  A Cr : Circuit N
  A  = ΛH (₁₊ m)
  Cr = X ↑ ↑ • (Ex ↑ • Ex ↓) • A • (Ex ↓ • Ex ↑) • X ↑ ↑

  ------------------------------------------------------------------------
  -- The H-pattern of H_[3,2] H_[4,5]

  G₃ : Bits N
  G₃ = false ∷ true ∷ false ∷ t

  cong-hpat : ∀ {a a′ b b′ c c′ e e′ : Bits N} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ →
              hpat a b c e ≡ hpat a′ b′ c′ e′
  cong-hpat Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  pat3245 : hpat (gcode {m} 3) (gcode 2) (gcode 4) (gcode 5) ≡ just (0 , 2)
  pat3245 = Eq.trans (cong-hpat g3 g2 g4 g5)
                     (hpat-flips G₃ 0 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) (λ ()) Eq.refl Eq.refl)

  H₃ : Circuit N
  H₃ = mcH (layoutH (gcode {m} 3) 0 2)

  d-h3 : (d ʷ) (hhℕ {N} 3 2 4 5) ≡ rev H₃
  d-h3 = d-hh-pat ₃ ₂ ₄ ₅ 0 2 Eq.refl pat3245

  L₃₂ : Layout N
  L₃₂ = tgtH ∷ ctrl true ∷ tgt ∷ layoutHFrom 3 0 2 t

  lay32 : layoutH (gcode {m} 3) 0 2 ≡ L₃₂
  lay32 = Eq.cong (λ g → layoutH {m} g 0 2) g3

  NY₀₂ : negs (layoutHFrom 3 0 2 t) ≡ NY
  NY₀₂ = Eq.trans (Eq.sym (negs-tail₀₂ t 0)) (negs-tail t 0)

  ------------------------------------------------------------------------
  -- H_[3,2] H_[4,5] between the negations T

  X₂-NY : X ↑ ↑ • NY ↑ ↑ ↑ ≈ NY ↑ ↑ ↑ • X ↑ ↑
  X₂-NY = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ NY))

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

  -- X on the wires 3 … is X on the wires 2 … times X on wire 2.
  R3 : NY ↑ ↑ ↑ ≈ X ↑ ↑ • T
  R3 = sym (trans (sym assoc) (trans (front _ X₂²) left-unit))

  L3 : NY ↑ ↑ ↑ ≈ T • X ↑ ↑
  L3 = trans R3 (trans (back _ X₂-NY) (sym assoc))

  h3-≡ : H₃ ≡ NY ↑ ↑ ↑ • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • NY ↑ ↑ ↑
  h3-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) lay32)
                  (Eq.cong (λ z → z ↑ ↑ ↑ • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • z ↑ ↑ ↑) NY₀₂)

  h3-form : H₃ ≈ CT.⟪ Cr ⟫
  h3-form = begin
    H₃
      ≈⟨ ≡→≈ h3-≡ ⟩
    NY ↑ ↑ ↑ • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • NY ↑ ↑ ↑
      ≈⟨ back _ (cong (back _ right-unit) (trans left-unit (back _ (trans left-unit (front _ (front _ left-unit)))))) ⟩
    NY ↑ ↑ ↑ • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • NY ↑ ↑ ↑
      ≈⟨ cong L3 (back _ (back _ (back _ R3))) ⟩
    (T • X ↑ ↑) • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • (X ↑ ↑ • T)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • (□ • □)) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    T • Cr • T ∎

  ------------------------------------------------------------------------
  -- The unreversed rule

  unrev : H₃ • gadget {m} ≈ dXX {m} 0 3 1 2 • H₃ • dXX {m} 0 3 1 2
  unrev = begin
    H₃ • gadget                              ≈⟨ cong h3-form gadget-form ⟩
    CT.⟪ Cr ⟫ • CT.⟪ S ⟫                     ≈⟨ CT.⟪⟫-≈ core (CT.⟪⟫-•₂ refl refl) (CT.⟪⟫-•₃ refl refl refl) ⟩
    CT.⟪ Cc ⟫ • CT.⟪ Cr ⟫ • CT.⟪ Cc ⟫        ≈⟨ sym (cong xx-form (cong h3-form xx-form)) ⟩
    dXX 0 3 1 2 • H₃ • dXX 0 3 1 2 ∎

------------------------------------------------------------------------
-- (43)

e43 : (d ʷ) (hhℕ {N} 0 1 3 2 • hhℕ 3 2 4 5) ≈ (d ʷ) (xxℕ {N} 0 3 1 2 • hhℕ 3 2 4 5 • xxℕ 0 3 1 2)
e43 = begin
  (d ʷ) (hhℕ 0 1 3 2 • hhℕ 3 2 4 5)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-hh0132 d-h3) ⟩
  rev gadget • rev H₃
    ≈⟨ rev-cong unrev ⟩
  rev (dXX 0 3 1 2 • H₃ • dXX 0 3 1 2)
    ≈⟨ by-passoc ((□ • □) • □) (□ • □ • □) Eq.refl ⟩
  rev (dXX 0 3 1 2) • rev H₃ • rev (dXX 0 3 1 2)
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-xx (Eq.cong₂ _•_ d-h3 d-xx))) ⟩
  (d ʷ) (xxℕ 0 3 1 2 • hhℕ 3 2 4 5 • xxℕ 0 3 1 2) ∎
