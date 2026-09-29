------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (46) of Figure 8 (Clément, Appendix E.5)
--
-- (46) is
--   H_[0,1]H_[7,6] · H_[0,3]H_[1,2] · H_[3,4]H_[2,5] · H_[3,2]H_[4,5] ·
--   H_[7,6]H_[4,5] · (−1)_[2](−1)_[3] · H_[3,4]H_[2,5] · H_[0,3]H_[1,2]
--   = H_[0,3]H_[1,2] · H_[3,4]H_[2,5] · (−1)_[2](−1)_[3] · H_[7,6]H_[4,5] ·
--     H_[3,2]H_[4,5] · H_[3,4]H_[2,5] · H_[0,3]H_[1,2] · H_[0,1]H_[7,6].
-- Every Hadamard pair has an H-pattern — (0 , 2), (1 , 0), (2 , 0),
-- (0 , 2) and (0 , 1) — so decodes to a placed H gate (`d-hh-pat`), and
-- the sign pair on 2 3 to one box.  All six share the negations of the
-- wires 3 … (`N3`, X where t is white), which are conjugated away; what
-- is left are the gates of Lemma88.Letters46, and the rule is the
-- module's parameter `core`, which GeneralN.Canon46 proves.  The
-- decodings are reversed, and reversal is a congruence (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 using (Core46)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule46
  {m : ℕ}
  (core : Core46 {m})
  where

open import Data.Bool using (true ; false)
open import Data.Maybe using (just)
open import Data.Nat using (zero ; suc ; s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (i₂ ; i₃ ; toℕ-i₂ ; toℕ-i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zzℕ ; hhℕ ; hpat)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (ctrl ; tgt ; tgtH ; Layout ; negs ; conj₁ ; conj₂ ; mcH ; ΛH)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZZ ; gcode ; layoutH ; layoutHFrom ; slot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters using (hpat-flips)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh-pat)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; g0 ; g1 ; g2 ; g3 ; g4 ; g5 ; g6 ; g7 ; L₂ ; lay2 ;
         negs-tail ; negs-tail₁₀ ; negs-tail₀₂ ; negs² ; NY)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 {m}
  using (h0312 ; h3425 ; z23 ; h7645 ; h3245 ; h0176)

private
  N : ℕ
  N = ₃₊ m

  variable
    k : ℕ

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  A Λ : Circuit N
  A = ΛH (₁₊ m)
  Λ = Λ□ (₂₊ m)

  ------------------------------------------------------------------------
  -- The common negations

  N3 : Circuit N
  N3 = NY ↑ ↑ ↑

  N3² : N3 • N3 ≈ ε
  N3² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (negs² (layoutHFrom 3 0 1 t))))

  module C3 = Conj N3 N3²

  X₁-N3 : X ↑ • N3 ≈ N3 • X ↑
  X₁-N3 = lemma-cong↑ _ _ (X-↑ (NY ↑))

  X₂-N3 : X ↑ ↑ • N3 ≈ N3 • X ↑ ↑
  X₂-N3 = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ NY))

  -- A gate between the negations with a negation of its own that they
  -- commute with.
  wrap : ∀ {a mid c} → mid ≈ c → a • N3 ≈ N3 • a → (a • N3) • mid • (a • N3) ≈ C3.⟪ a • c • a ⟫
  wrap {a} {mid} {c} e ac = begin
    (a • N3) • mid • (a • N3)     ≈⟨ cong ac (front _ e) ⟩
    (N3 • a) • c • (a • N3)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    N3 • (a • c • a) • N3 ∎

  -- On the wires 3 … the layouts of the H-patterns (2 , 0) negate the
  -- white controls, as every other layout does.
  negs-tail₂₀ : ∀ (s : Bits k) w → negs (zipWith slot s s) ≡ negs (layoutHFrom (₃₊ w) 2 0 s)
  negs-tail₂₀ []          w = Eq.refl
  negs-tail₂₀ (true ∷ s)  w = Eq.cong _↑ (negs-tail₂₀ s (suc w))
  negs-tail₂₀ (false ∷ s) w = Eq.cong (λ z → X • z ↑) (negs-tail₂₀ s (suc w))

  cong-hpat : ∀ {a a′ b b′ c c′ e e′ : Bits N} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ →
              hpat a b c e ≡ hpat a′ b′ c′ e′
  cong-hpat Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  G₀ G₃ G₇ : Bits N
  G₀ = false ∷ false ∷ false ∷ t
  G₃ = false ∷ true ∷ false ∷ t
  G₇ = false ∷ false ∷ true ∷ t

  ------------------------------------------------------------------------
  -- H_[0,3] H_[1,2]: H-pattern (1 , 0)

  H0312 : Circuit N
  H0312 = mcH (layoutH (gcode {m} 0) 1 0)

  d0312 : (d ʷ) (hhℕ {N} 0 3 1 2) ≡ rev H0312
  d0312 = d-hh-pat ₀ ₃ ₁ ₂ 1 0 Eq.refl
            (Eq.trans (cong-hpat g0 g3 g1 g2)
                      (hpat-flips G₀ 1 0 (s≤s (s≤s z≤n)) (s≤s z≤n) (λ ()) Eq.refl Eq.refl))

  H0312-≡ : H0312 ≡ (X ↑ ↑ • N3) • ε • ε • A • ε • ε • (X ↑ ↑ • N3)
  H0312-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) (Eq.cong (λ g → layoutH {m} g 1 0) g0))
                     (Eq.cong (λ z → (X ↑ ↑ • z ↑ ↑ ↑) • ε • ε • A • ε • ε • (X ↑ ↑ • z ↑ ↑ ↑))
                              (Eq.trans (Eq.sym (negs-tail₁₀ t 0)) (negs-tail t 0)))

  f0312 : H0312 ≈ C3.⟪ h0312 ⟫
  f0312 = begin
    H0312
      ≈⟨ ≡→≈ H0312-≡ ⟩
    (X ↑ ↑ • N3) • ε • ε • A • ε • ε • (X ↑ ↑ • N3)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □ • □ • (□ • □)) ((□ • □) • (□ • □ • □ • □ • □) • (□ • □)) Eq.refl ⟩
    (X ↑ ↑ • N3) • (ε • ε • A • ε • ε) • (X ↑ ↑ • N3)
      ≈⟨ wrap (trans left-unit (trans left-unit (trans (back _ left-unit) right-unit))) X₂-N3 ⟩
    C3.⟪ h0312 ⟫ ∎

  ------------------------------------------------------------------------
  -- H_[3,4] H_[2,5]: H-pattern (2 , 0)

  H3425 : Circuit N
  H3425 = mcH (layoutH (gcode {m} 3) 2 0)

  d3425 : (d ʷ) (hhℕ {N} 3 4 2 5) ≡ rev H3425
  d3425 = d-hh-pat ₃ ₄ ₂ ₅ 2 0 Eq.refl
            (Eq.trans (cong-hpat g3 g4 g2 g5)
                      (hpat-flips G₃ 2 0 (s≤s (s≤s (s≤s z≤n))) (s≤s z≤n) (λ ()) Eq.refl Eq.refl))

  H3425-≡ : H3425 ≡ N3 • ε • (Ex ↑ • ε) • A • (ε • Ex ↑) • ε • N3
  H3425-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) (Eq.cong (λ g → layoutH {m} g 2 0) g3))
                     (Eq.cong (λ z → z ↑ ↑ ↑ • ε • (Ex ↑ • ε) • A • (ε • Ex ↑) • ε • z ↑ ↑ ↑)
                              (Eq.trans (Eq.sym (negs-tail₂₀ t 0)) (negs-tail t 0)))

  f3425 : H3425 ≈ C3.⟪ h3425 ⟫
  f3425 = begin
    H3425
      ≈⟨ ≡→≈ H3425-≡ ⟩
    N3 • ε • (Ex ↑ • ε) • A • (ε • Ex ↑) • ε • N3
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    N3 • (ε • (Ex ↑ • ε) • A • (ε • Ex ↑) • ε) • N3
      ≈⟨ back _ (front _ (by-assoc Eq.refl)) ⟩
    C3.⟪ h3425 ⟫ ∎

  ------------------------------------------------------------------------
  -- (−1)_[2] (−1)_[3]: the chain of one box

  d23 : (d ʷ) (zzℕ {N} 2 3) ≡ rev (dZZ {m} 2 3)
  d23 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (Eq.cong₂ zzℕ (Eq.sym toℕ-i₂) (Eq.sym toℕ-i₃)) (zzℕ-zz i₂ i₃)))
                 (Eq.cong₂ (λ a b → rev (dZZ {m} a b)) toℕ-i₂ toℕ-i₃)

  Z23-≡ : dZZ {m} 2 3 ≡ ((X ↑ ↑ • N3) • ε • Λ • ε • (X ↑ ↑ • N3)) • ε
  Z23-≡ = Eq.trans (Eq.cong (λ L → conj₁ L Λ • ε) lay2)
                   (Eq.cong (λ z → ((X ↑ ↑ • z ↑ ↑ ↑) • ε • Λ • ε • (X ↑ ↑ • z ↑ ↑ ↑)) • ε) (negs-tail t 0))

  f23 : dZZ {m} 2 3 ≈ C3.⟪ z23 ⟫
  f23 = begin
    dZZ 2 3
      ≈⟨ ≡→≈ Z23-≡ ⟩
    ((X ↑ ↑ • N3) • ε • Λ • ε • (X ↑ ↑ • N3)) • ε
      ≈⟨ right-unit ⟩
    (X ↑ ↑ • N3) • ε • Λ • ε • (X ↑ ↑ • N3)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • (□ • □)) ((□ • □) • (□ • □ • □) • (□ • □)) Eq.refl ⟩
    (X ↑ ↑ • N3) • (ε • Λ • ε) • (X ↑ ↑ • N3)
      ≈⟨ wrap (trans left-unit right-unit) X₂-N3 ⟩
    C3.⟪ z23 ⟫ ∎

  ------------------------------------------------------------------------
  -- H_[7,6] H_[4,5]: H-pattern (0 , 1)

  H7645 : Circuit N
  H7645 = mcH (layoutH (gcode {m} 7) 0 1)

  d7645 : (d ʷ) (hhℕ {N} 7 6 4 5) ≡ rev H7645
  d7645 = d-hh-pat ₇ ₆ ₄ ₅ 0 1 Eq.refl
            (Eq.trans (cong-hpat g7 g6 g4 g5)
                      (hpat-flips G₇ 0 1 (s≤s z≤n) (s≤s (s≤s z≤n)) (λ ()) Eq.refl Eq.refl))

  H7645-≡ : H7645 ≡ N3 • (Ex • ε) • ε • A • ε • (ε • Ex) • N3
  H7645-≡ = Eq.cong (λ L → conj₂ L A) (Eq.cong (λ g → layoutH {m} g 0 1) g7)

  f7645 : H7645 ≈ C3.⟪ h7645 ⟫
  f7645 = begin
    H7645
      ≈⟨ ≡→≈ H7645-≡ ⟩
    N3 • (Ex • ε) • ε • A • ε • (ε • Ex) • N3
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    N3 • ((Ex • ε) • ε • A • ε • (ε • Ex)) • N3
      ≈⟨ back _ (front _ (by-assoc Eq.refl)) ⟩
    C3.⟪ h7645 ⟫ ∎

  ------------------------------------------------------------------------
  -- H_[3,2] H_[4,5]: H-pattern (0 , 2)

  H3245 : Circuit N
  H3245 = mcH (layoutH (gcode {m} 3) 0 2)

  d3245 : (d ʷ) (hhℕ {N} 3 2 4 5) ≡ rev H3245
  d3245 = d-hh-pat ₃ ₂ ₄ ₅ 0 2 Eq.refl
            (Eq.trans (cong-hpat g3 g2 g4 g5)
                      (hpat-flips G₃ 0 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) (λ ()) Eq.refl Eq.refl))

  mid02 : (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) ≈ (Ex ↑ • Ex ↓) • A • (Ex ↓ • Ex ↑)
  mid02 = by-assoc Eq.refl

  H3245-≡ : H3245 ≡ N3 • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • N3
  H3245-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) (Eq.cong (λ g → layoutH {m} g 0 2) g3))
                     (Eq.cong (λ z → z ↑ ↑ ↑ • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • z ↑ ↑ ↑)
                              (Eq.trans (Eq.sym (negs-tail₀₂ t 0)) (negs-tail t 0)))

  f3245 : H3245 ≈ C3.⟪ h3245 ⟫
  f3245 = begin
    H3245
      ≈⟨ ≡→≈ H3245-≡ ⟩
    N3 • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • N3
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    N3 • ((Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑)) • N3
      ≈⟨ back _ (front _ mid02) ⟩
    C3.⟪ h3245 ⟫ ∎

  ------------------------------------------------------------------------
  -- H_[0,1] H_[7,6]: H-pattern (0 , 2)

  H0176 : Circuit N
  H0176 = mcH (layoutH (gcode {m} 0) 0 2)

  d0176 : (d ʷ) (hhℕ {N} 0 1 7 6) ≡ rev H0176
  d0176 = d-hh-pat ₀ ₁ ₇ ₆ 0 2 Eq.refl
            (Eq.trans (cong-hpat g0 g1 g7 g6)
                      (hpat-flips G₀ 0 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) (λ ()) Eq.refl Eq.refl))

  H0176-≡ : H0176 ≡ (X ↑ • N3) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • (X ↑ • N3)
  H0176-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) (Eq.cong (λ g → layoutH {m} g 0 2) g0))
                     (Eq.cong (λ z → (X ↑ • z ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) •
                                     (X ↑ • z ↑ ↑ ↑))
                              (Eq.trans (Eq.sym (negs-tail₀₂ t 0)) (negs-tail t 0)))

  f0176 : H0176 ≈ C3.⟪ h0176 ⟫
  f0176 = begin
    H0176
      ≈⟨ ≡→≈ H0176-≡ ⟩
    (X ↑ • N3) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • (X ↑ • N3)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □ • □ • (□ • □)) ((□ • □) • (□ • □ • □ • □ • □) • (□ • □)) Eq.refl ⟩
    (X ↑ • N3) • ((Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑)) • (X ↑ • N3)
      ≈⟨ wrap mid02 X₁-N3 ⟩
    C3.⟪ h0176 ⟫ ∎

  ------------------------------------------------------------------------
  -- The unreversed rule

  unrev : H0312 • H3425 • dZZ 2 3 • H7645 • H3245 • H3425 • H0312 • H0176
        ≈ H0176 • H0312 • H3425 • H3245 • H7645 • dZZ 2 3 • H3425 • H0312
  unrev = begin
    H0312 • H3425 • dZZ 2 3 • H7645 • H3245 • H3425 • H0312 • H0176
      ≈⟨ cong f0312 (cong f3425 (cong f23 (cong f7645 (cong f3245 (cong f3425 (cong f0312 f0176)))))) ⟩
    C3.⟪ h0312 ⟫ • C3.⟪ h3425 ⟫ • C3.⟪ z23 ⟫ • C3.⟪ h7645 ⟫ • C3.⟪ h3245 ⟫ • C3.⟪ h3425 ⟫ •
    C3.⟪ h0312 ⟫ • C3.⟪ h0176 ⟫
      ≈⟨ C3.⟪⟫-≈ core (C3.⟪⟫-•₄ refl refl refl (C3.⟪⟫-•₅ refl refl refl refl refl))
                      (C3.⟪⟫-•₄ refl refl refl (C3.⟪⟫-•₅ refl refl refl refl refl)) ⟩
    C3.⟪ h0176 ⟫ • C3.⟪ h0312 ⟫ • C3.⟪ h3425 ⟫ • C3.⟪ h3245 ⟫ • C3.⟪ h7645 ⟫ • C3.⟪ z23 ⟫ •
    C3.⟪ h3425 ⟫ • C3.⟪ h0312 ⟫
      ≈⟨ sym (cong f0176 (cong f0312 (cong f3425 (cong f3245 (cong f7645 (cong f23 (cong f3425 f0312))))))) ⟩
    H0176 • H0312 • H3425 • H3245 • H7645 • dZZ 2 3 • H3425 • H0312 ∎

------------------------------------------------------------------------
-- (46)

e46 : (d ʷ) (hhℕ {N} 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • hhℕ 3 2 4 5 • hhℕ 7 6 4 5 •
             zzℕ 2 3 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2)
    ≈ (d ʷ) (hhℕ {N} 0 3 1 2 • hhℕ 3 4 2 5 • zzℕ 2 3 • hhℕ 7 6 4 5 • hhℕ 3 2 4 5 •
             hhℕ 3 4 2 5 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6)
e46 = begin
  (d ʷ) (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • hhℕ 3 2 4 5 • hhℕ 7 6 4 5 •
         zzℕ 2 3 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ d0176 (Eq.cong₂ _•_ d0312 (Eq.cong₂ _•_ d3425 (Eq.cong₂ _•_ d3245
             (Eq.cong₂ _•_ d7645 (Eq.cong₂ _•_ d23 (Eq.cong₂ _•_ d3425 d0312))))))) ⟩
  rev H0176 • rev H0312 • rev H3425 • rev H3245 • rev H7645 • rev (dZZ 2 3) • rev H3425 • rev H0312
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (((((((□ • □) • □) • □) • □) • □) • □) • □) Eq.refl ⟩
  rev (H0312 • H3425 • dZZ 2 3 • H7645 • H3245 • H3425 • H0312 • H0176)
    ≈⟨ rev-cong unrev ⟩
  rev (H0176 • H0312 • H3425 • H3245 • H7645 • dZZ 2 3 • H3425 • H0312)
    ≈⟨ by-passoc (((((((□ • □) • □) • □) • □) • □) • □) • □) (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
  rev H0312 • rev H3425 • rev (dZZ 2 3) • rev H7645 • rev H3245 • rev H3425 • rev H0312 • rev H0176
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d0312 (Eq.cong₂ _•_ d3425 (Eq.cong₂ _•_ d23 (Eq.cong₂ _•_ d7645
             (Eq.cong₂ _•_ d3245 (Eq.cong₂ _•_ d3425 (Eq.cong₂ _•_ d0312 d0176)))))))) ⟩
  (d ʷ) (hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • zzℕ 2 3 • hhℕ 7 6 4 5 • hhℕ 3 2 4 5 •
         hhℕ 3 4 2 5 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ∎
