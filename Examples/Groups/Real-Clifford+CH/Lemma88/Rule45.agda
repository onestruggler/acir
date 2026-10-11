------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (45) of Figure 8 (Clément, Appendix E.5)
--
-- (45) is H_[0,1] H_[7,6] · H_[0,3] H_[1,2] · H_[0,1] H_[7,6] · (−1)_[0] (−1)_[1]
--         · H_[0,3] H_[1,2]  =  the same letters in the reverse order.
-- Decoded, all three kinds of letter are gates with white controls on
-- the wires 3 …: H_[0,1] H_[7,6] (H-pattern (0 , 2)) is the H gate on
-- wire 0 with its box wire on wire 2, white on wire 1; H_[0,3] H_[1,2]
-- (H-pattern (1 , 0)) the H gate on wire 1 with its box wire on wire 0
-- — ΛH itself; and the sign pair the box on wire 0, white on wire 1.
-- They share the negations of the wires 2 … (Layout's `T`), which are
-- conjugated away; what is left is the module's parameter `core`, which
-- GeneralN.Canon45 gives at every width from five on.  The decodings are
-- reversed, and reversal is a congruence (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule45
  {m : ℕ}
  (core : (₃₊ m) ⊢ ΛH (₁₊ m) • (X ↑ • Λ□ (₂₊ m) • X ↑) •
                     ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
                     ΛH (₁₊ m) •
                     ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑))
                  ≈ ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
                     ΛH (₁₊ m) •
                     ((X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)) •
                     (X ↑ • Λ□ (₂₊ m) • X ↑) • ΛH (₁₊ m))
  where

open import Data.Bool using (false)
open import Data.Maybe using (just)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (i₀ ; i₁ ; toℕ-i₀ ; toℕ-i₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zzℕ ; hhℕ ; hpat)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; tgtH ; Layout ; negs ; conj₁ ; conj₂ ; mcH)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZZ ; gcode ; layoutH ; layoutHFrom)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters using (hpat-flips)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh-pat)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; g0 ; g1 ; g2 ; g3 ; g6 ; g7 ; L₀ ; lay0 ; negs-tail ; negs-tail₁₀ ; negs-tail₀₂ ;
         NY ; T ; module CT)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  A Λ Zc XX Cw : Circuit N
  A  = ΛH (₁₊ m)
  Λ  = Λ□ (₂₊ m)
  Zc = X ↑ • Λ • X ↑
  XX = X ↑ • X ↑ ↑
  Cw = XX • (Ex ↑ • Ex ↓) • A • (Ex ↓ • Ex ↑) • XX

  ------------------------------------------------------------------------
  -- The H-patterns

  G₀ : Bits N
  G₀ = false ∷ false ∷ false ∷ t

  cong-hpat : ∀ {a a′ b b′ c c′ e e′ : Bits N} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ →
              hpat a b c e ≡ hpat a′ b′ c′ e′
  cong-hpat Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  pat0176 : hpat (gcode {m} 0) (gcode 1) (gcode 7) (gcode 6) ≡ just (0 , 2)
  pat0176 = Eq.trans (cong-hpat g0 g1 g7 g6)
                     (hpat-flips G₀ 0 2 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) (λ ()) Eq.refl Eq.refl)

  pat0312 : hpat (gcode {m} 0) (gcode 3) (gcode 1) (gcode 2) ≡ just (1 , 0)
  pat0312 = Eq.trans (cong-hpat g0 g3 g1 g2)
                     (hpat-flips G₀ 1 0 (s≤s (s≤s z≤n)) (s≤s z≤n) (λ ()) Eq.refl Eq.refl)

  ------------------------------------------------------------------------
  -- The decoded letters

  H₁ H₂ : Circuit N
  H₁ = mcH (layoutH (gcode {m} 0) 0 2)
  H₂ = mcH (layoutH (gcode {m} 0) 1 0)

  d-h1 : (d ʷ) (hhℕ {N} 0 1 7 6) ≡ rev H₁
  d-h1 = d-hh-pat ₀ ₁ ₇ ₆ 0 2 Eq.refl pat0176

  d-h2 : (d ʷ) (hhℕ {N} 0 3 1 2) ≡ rev H₂
  d-h2 = d-hh-pat ₀ ₃ ₁ ₂ 1 0 Eq.refl pat0312

  d-zz01 : (d ʷ) (zzℕ {N} 0 1) ≡ rev (dZZ {m} 0 1)
  d-zz01 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (Eq.cong₂ zzℕ (Eq.sym toℕ-i₀) (Eq.sym toℕ-i₁)) (zzℕ-zz i₀ i₁)))
                    (Eq.cong₂ (λ a b → rev (dZZ {m} a b)) toℕ-i₀ toℕ-i₁)

  -- The layouts.
  L₀₂ L₁₀ : Layout N
  L₀₂ = tgtH ∷ ctrl false ∷ tgt ∷ layoutHFrom 3 0 2 t
  L₁₀ = tgt ∷ tgtH ∷ ctrl false ∷ layoutHFrom 3 1 0 t

  lay02 : layoutH (gcode {m} 0) 0 2 ≡ L₀₂
  lay02 = Eq.cong (λ g → layoutH {m} g 0 2) g0

  lay10 : layoutH (gcode {m} 0) 1 0 ≡ L₁₀
  lay10 = Eq.cong (λ g → layoutH {m} g 1 0) g0

  NY₀₂ : negs (layoutHFrom 3 0 2 t) ≡ NY
  NY₀₂ = Eq.trans (Eq.sym (negs-tail₀₂ t 0)) (negs-tail t 0)

  NY₁₀ : negs (layoutHFrom 3 1 0 t) ≡ NY
  NY₁₀ = Eq.trans (Eq.sym (negs-tail₁₀ t 0)) (negs-tail t 0)

  ------------------------------------------------------------------------
  -- X on the wires 1 … and 2 …

  X₁₂ : X ↑ • X ↑ ↑ ≈ X ↑ ↑ • X ↑
  X₁₂ = lemma-cong↑ _ _ (X-↑ X)

  X₁-NY : X ↑ • NY ↑ ↑ ↑ ≈ NY ↑ ↑ ↑ • X ↑
  X₁-NY = lemma-cong↑ _ _ (X-↑ (NY ↑))

  X₂-NY : X ↑ ↑ • NY ↑ ↑ ↑ ≈ NY ↑ ↑ ↑ • X ↑ ↑
  X₂-NY = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ NY))

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

  -- X on the wires 1 3 … is X on the wires 1 2 times T, in either order.
  LT : X ↑ • NY ↑ ↑ ↑ ≈ T • XX
  LT = begin
    X ↑ • NY ↑ ↑ ↑                              ≈⟨ back _ (sym (trans (sym assoc) (trans (front _ X₂²) left-unit))) ⟩
    X ↑ • X ↑ ↑ • X ↑ ↑ • NY ↑ ↑ ↑              ≈⟨ back _ (back _ X₂-NY) ⟩
    X ↑ • X ↑ ↑ • NY ↑ ↑ ↑ • X ↑ ↑              ≈⟨ trans (sym assoc) (trans (front _ X₁₂) assoc) ⟩
    X ↑ ↑ • X ↑ • NY ↑ ↑ ↑ • X ↑ ↑              ≈⟨ back _ (trans (sym assoc) (front _ X₁-NY)) ⟩
    X ↑ ↑ • (NY ↑ ↑ ↑ • X ↑) • X ↑ ↑            ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    T • XX ∎

  RT : X ↑ • NY ↑ ↑ ↑ ≈ XX • T
  RT = begin
    X ↑ • NY ↑ ↑ ↑                              ≈⟨ back _ (sym (trans (sym assoc) (trans (front _ X₂²) left-unit))) ⟩
    X ↑ • X ↑ ↑ • X ↑ ↑ • NY ↑ ↑ ↑              ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    XX • T ∎

  X₁T : X ↑ • T ≈ T • X ↑
  X₁T = begin
    X ↑ • X ↑ ↑ • NY ↑ ↑ ↑        ≈⟨ trans (sym assoc) (front _ X₁₂) ⟩
    (X ↑ ↑ • X ↑) • NY ↑ ↑ ↑      ≈⟨ trans assoc (back _ X₁-NY) ⟩
    X ↑ ↑ • NY ↑ ↑ ↑ • X ↑        ≈⟨ sym assoc ⟩
    (X ↑ ↑ • NY ↑ ↑ ↑) • X ↑ ∎

  ------------------------------------------------------------------------
  -- Each letter between the negations T

  h1-≡ : H₁ ≡ (X ↑ • NY ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • (X ↑ • NY ↑ ↑ ↑)
  h1-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) lay02)
                  (Eq.cong (λ z → (X ↑ • z ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • (X ↑ • z ↑ ↑ ↑))
                           NY₀₂)

  h1-form : H₁ ≈ CT.⟪ Cw ⟫
  h1-form = begin
    H₁
      ≈⟨ ≡→≈ h1-≡ ⟩
    (X ↑ • NY ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • ε • A • ε • ((ε • Ex) • Ex ↑) • (X ↑ • NY ↑ ↑ ↑)
      ≈⟨ back _ (cong (back _ right-unit) (trans left-unit (back _ (trans left-unit (front _ (front _ left-unit)))))) ⟩
    (X ↑ • NY ↑ ↑ ↑) • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • (X ↑ • NY ↑ ↑ ↑)
      ≈⟨ cong LT (back _ (back _ (back _ RT))) ⟩
    (T • XX) • (Ex ↑ • Ex) • A • (Ex • Ex ↑) • (XX • T)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • (□ • □)) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    T • Cw • T ∎

  h2-≡ : H₂ ≡ T • ε • ε • A • ε • ε • T
  h2-≡ = Eq.trans (Eq.cong (λ L → conj₂ L A) lay10)
                  (Eq.cong (λ z → (X ↑ ↑ • z ↑ ↑ ↑) • ε • ε • A • ε • ε • (X ↑ ↑ • z ↑ ↑ ↑)) NY₁₀)

  h2-form : H₂ ≈ CT.⟪ A ⟫
  h2-form = trans (≡→≈ h2-≡) (back _ (trans left-unit (trans left-unit (back _ (trans left-unit left-unit)))))

  negs-L₀ : negs L₀ ≡ X ↑ • T
  negs-L₀ = Eq.cong (λ z → X ↑ • X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  box-≡ : dZZ {m} 0 1 ≡ ((X ↑ • T) • ε • Λ • ε • (X ↑ • T)) • ε
  box-≡ = Eq.trans (Eq.cong (λ L → conj₁ L Λ • ε) lay0) (Eq.cong (λ z → (z • ε • Λ • ε • z) • ε) negs-L₀)

  box-form : dZZ {m} 0 1 ≈ CT.⟪ Zc ⟫
  box-form = begin
    dZZ 0 1                                          ≈⟨ ≡→≈ box-≡ ⟩
    ((X ↑ • T) • ε • Λ • ε • (X ↑ • T)) • ε          ≈⟨ right-unit ⟩
    (X ↑ • T) • ε • Λ • ε • (X ↑ • T)                ≈⟨ back _ (trans left-unit (back _ left-unit)) ⟩
    (X ↑ • T) • Λ • (X ↑ • T)                        ≈⟨ front _ X₁T ⟩
    (T • X ↑) • Λ • (X ↑ • T)                        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    T • (X ↑ • Λ • X ↑) • T ∎

  ------------------------------------------------------------------------
  -- The unreversed rule

  unrev : H₂ • dZZ {m} 0 1 • H₁ • H₂ • H₁ ≈ H₁ • H₂ • H₁ • dZZ {m} 0 1 • H₂
  unrev = begin
    H₂ • dZZ 0 1 • H₁ • H₂ • H₁
      ≈⟨ cong h2-form (cong box-form (cong h1-form (cong h2-form h1-form))) ⟩
    CT.⟪ A ⟫ • CT.⟪ Zc ⟫ • CT.⟪ Cw ⟫ • CT.⟪ A ⟫ • CT.⟪ Cw ⟫
      ≈⟨ CT.⟪⟫-≈ core (CT.⟪⟫-•₂ refl (CT.⟪⟫-•₄ refl refl refl refl))
                      (CT.⟪⟫-•₂ refl (CT.⟪⟫-•₄ refl refl refl refl)) ⟩
    CT.⟪ Cw ⟫ • CT.⟪ A ⟫ • CT.⟪ Cw ⟫ • CT.⟪ Zc ⟫ • CT.⟪ A ⟫
      ≈⟨ sym (cong h1-form (cong h2-form (cong h1-form (cong box-form h2-form)))) ⟩
    H₁ • H₂ • H₁ • dZZ 0 1 • H₂ ∎

------------------------------------------------------------------------
-- (45)

e45 : (d ʷ) (hhℕ {N} 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6 • zzℕ 0 1 • hhℕ 0 3 1 2)
    ≈ (d ʷ) (hhℕ {N} 0 3 1 2 • zzℕ 0 1 • hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6)
e45 = begin
  (d ʷ) (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6 • zzℕ 0 1 • hhℕ 0 3 1 2)
    ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-h1 (Eq.cong₂ _•_ d-h2 (Eq.cong₂ _•_ d-h1 (Eq.cong₂ _•_ d-zz01 d-h2)))) ⟩
  rev H₁ • rev H₂ • rev H₁ • rev (dZZ 0 1) • rev H₂
    ≈⟨ by-passoc (□ • □ • □ • □ • □) ((((□ • □) • □) • □) • □) Eq.refl ⟩
  rev (H₂ • dZZ 0 1 • H₁ • H₂ • H₁)
    ≈⟨ rev-cong unrev ⟩
  rev (H₁ • H₂ • H₁ • dZZ 0 1 • H₂)
    ≈⟨ by-passoc ((((□ • □) • □) • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  rev H₂ • rev (dZZ 0 1) • rev H₁ • rev H₂ • rev H₁
    ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-h2 (Eq.cong₂ _•_ d-zz01 (Eq.cong₂ _•_ d-h1 (Eq.cong₂ _•_ d-h2 d-h1))))) ⟩
  (d ʷ) (hhℕ 0 3 1 2 • zzℕ 0 1 • hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ∎
