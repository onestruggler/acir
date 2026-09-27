------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (40) of Figure 8 (Clément, Appendix E.5)
--
-- (40) is (−1)_[3] (−1)_[4] H_[0,1] H_[3,2]
--       = H_[0,1] H_[3,2] (−1)_[3] (−1)_[4] (−1)_[2] X_[2,3].
-- Decoded, the sign pair is the box on wire 2, white on wire 0 and black
-- on wire 1 (the codes of 3 and 4 differ on wire 2), the Hadamard pair
-- is Definition 8.3's gadget (the H gate on wire 0 with its box wire 1),
-- and (−1)_[2] X_[2,3] is the multi-controlled ZX on wire 0, black on
-- wire 1, white on wire 2 — all three white on the wires 3 ….  They
-- share the negations of the wires 2 … (Layout's `T`), which are
-- conjugated away; the box keeps X on the wires 0 2 (`Btd`), and what is
-- left is the module's parameter `core`, which GeneralN.Canon40 gives at
-- every width from five on.  The decodings are reversed, and reversal
-- is a congruence (`rev-cong`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule40
  {m : ℕ}
  (core : (₃₊ m) ⊢ (Ex ↓ • ΛH (₁₊ m) • Ex ↓) •
                     ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) • Ex ↑) • (X • X ↑ ↑))
                  ≈ ΛZX (₂₊ m) •
                     ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ (₂₊ m) • Ex ↓) • Ex ↑) • (X • X ↑ ↑)) •
                     (Ex ↓ • ΛH (₁₊ m) • Ex ↓))
  where

open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (_^_)
open import Notations using (₄)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (i₂ ; i₃ ; toℕ-i₂ ; toℕ-i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz ; zxℕ-zx)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zzℕ ; zxℕ ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (negs ; conj₁)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZZ ; dZX ; gadget)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh0132 ; d-zx)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; L₂ ; lay2 ; L₃ ; lay3 ; negs-tail ; NY ; T ; module CT ; S ; gadget-form)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  Λ K Btd XX : Circuit N
  Λ   = Λ□ (₂₊ m)
  K   = Ex ↑ • (Ex ↓ • Λ • Ex ↓) • Ex ↑
  XX  = X • X ↑ ↑
  Btd = XX • K • XX

  ------------------------------------------------------------------------
  -- The decoded words

  negs-L₃ : negs L₃ ≡ X • NY ↑ ↑ ↑
  negs-L₃ = Eq.cong (λ z → X • z ↑ ↑ ↑) (negs-tail t 0)

  negs-L₂ : negs L₂ ≡ T
  negs-L₂ = Eq.cong (λ z → X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  box-≡ : dZZ {m} 3 4 ≡ ((X • NY ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • Λ • ((ε • Ex) • Ex ↑) • (X • NY ↑ ↑ ↑)) • ε
  box-≡ = Eq.trans (Eq.cong (λ L → conj₁ L Λ • ε) lay3)
                   (Eq.cong (λ z → (z • (Ex ↑ • Ex • ε) • Λ • ((ε • Ex) • Ex ↑) • z) • ε) negs-L₃)

  zx-≡ : dZX {m} 2 2 3 ≡ T • ε • ΛZX (₂₊ m) • ε • T
  zx-≡ = Eq.trans (Eq.cong (λ L → conj₁ L (ΛZX (₂₊ m))) lay2)
                  (Eq.cong (λ z → z • ε • ΛZX (₂₊ m) • ε • z) negs-L₂)

  -- X on the wires 0 and 3 … is X on the wires 0 2 times the negations
  -- T, in either order.
  X-X₂ : X • X ↑ ↑ ≈ X ↑ ↑ • X
  X-X₂ = X-↑ (X ↑)

  X-NY : X • NY ↑ ↑ ↑ ≈ NY ↑ ↑ ↑ • X
  X-NY = X-↑ (NY ↑ ↑)

  X₂-NY : X ↑ ↑ • NY ↑ ↑ ↑ ≈ NY ↑ ↑ ↑ • X ↑ ↑
  X₂-NY = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ NY))

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation.X²))

  LT : X • NY ↑ ↑ ↑ ≈ T • XX
  LT = begin
    X • NY ↑ ↑ ↑                            ≈⟨ back _ (sym (trans (sym assoc) (trans (front _ X₂²) left-unit))) ⟩
    X • X ↑ ↑ • X ↑ ↑ • NY ↑ ↑ ↑            ≈⟨ back _ (back _ X₂-NY) ⟩
    X • X ↑ ↑ • NY ↑ ↑ ↑ • X ↑ ↑            ≈⟨ trans (sym assoc) (trans (front _ X-X₂) assoc) ⟩
    X ↑ ↑ • X • NY ↑ ↑ ↑ • X ↑ ↑            ≈⟨ back _ (trans (sym assoc) (front _ X-NY)) ⟩
    X ↑ ↑ • (NY ↑ ↑ ↑ • X) • X ↑ ↑          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    T • XX ∎

  RT : X • NY ↑ ↑ ↑ ≈ XX • T
  RT = begin
    X • NY ↑ ↑ ↑                            ≈⟨ back _ (sym (trans (sym assoc) (trans (front _ X₂²) left-unit))) ⟩
    X • X ↑ ↑ • X ↑ ↑ • NY ↑ ↑ ↑            ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    XX • T ∎

  box-form : dZZ {m} 3 4 ≈ CT.⟪ Btd ⟫
  box-form = begin
    dZZ 3 4
      ≈⟨ ≡→≈ box-≡ ⟩
    ((X • NY ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • Λ • ((ε • Ex) • Ex ↑) • (X • NY ↑ ↑ ↑)) • ε
      ≈⟨ right-unit ⟩
    (X • NY ↑ ↑ ↑) • (Ex ↑ • Ex • ε) • Λ • ((ε • Ex) • Ex ↑) • (X • NY ↑ ↑ ↑)
      ≈⟨ back _ (cong (back _ right-unit) (back _ (front _ (front _ left-unit)))) ⟩
    (X • NY ↑ ↑ ↑) • (Ex ↑ • Ex) • Λ • (Ex • Ex ↑) • (X • NY ↑ ↑ ↑)
      ≈⟨ cong LT (back _ (back _ (back _ RT))) ⟩
    (T • XX) • (Ex ↑ • Ex) • Λ • (Ex • Ex ↑) • (XX • T)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • □ • (□ • □) • (□ • □))
                   (□ • (□ • (□ • (□ • □ • □) • □) • □) • □) Eq.refl ⟩
    T • Btd • T ∎

  zx-form : dZX {m} 2 2 3 ≈ CT.⟪ ΛZX (₂₊ m) ⟫
  zx-form = trans (≡→≈ zx-≡) (back _ (trans left-unit (back _ left-unit)))

  -- The unreversed rule.
  unrev : gadget {m} • dZZ {m} 3 4 ≈ dZX {m} 2 2 3 • dZZ {m} 3 4 • gadget {m}
  unrev = begin
    gadget • dZZ 3 4                              ≈⟨ cong gadget-form box-form ⟩
    CT.⟪ S ⟫ • CT.⟪ Btd ⟫                         ≈⟨ CT.⟪⟫-≈ core (CT.⟪⟫-• S Btd) (CT.⟪⟫-•₃ refl refl refl) ⟩
    CT.⟪ ΛZX (₂₊ m) ⟫ • CT.⟪ Btd ⟫ • CT.⟪ S ⟫     ≈⟨ sym (cong zx-form (cong box-form gadget-form)) ⟩
    dZX 2 2 3 • dZZ 3 4 • gadget ∎

  ------------------------------------------------------------------------
  -- The letters

  i₄ : Fin (2 ^ N)
  i₄ = fin8 {m} ₄

  toℕ-i₄ : toℕ i₄ ≡ 4
  toℕ-i₄ = toℕ-inject≤ ₄ _

  i₂≢i₃ : i₂ ≢ i₃
  i₂≢i₃ e with Eq.trans (Eq.sym toℕ-i₂) (Eq.trans (Eq.cong toℕ e) toℕ-i₃)
  ... | ()

  d-zz34 : (d ʷ) (zzℕ {N} 3 4) ≡ rev (dZZ {m} 3 4)
  d-zz34 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (Eq.cong₂ zzℕ (Eq.sym toℕ-i₃) (Eq.sym toℕ-i₄)) (zzℕ-zz i₃ i₄)))
                    (Eq.cong₂ (λ a b → rev (dZZ {m} a b)) toℕ-i₃ toℕ-i₄)

  d-zx223 : (d ʷ) (zxℕ {N} 2 2 3) ≡ rev (dZX {m} 2 2 3)
  d-zx223 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (Eq.cong₂ (λ a b → zxℕ a a b) (Eq.sym toℕ-i₂) (Eq.sym toℕ-i₃))
                                              (zxℕ-zx i₂ i₂ i₃)))
                     (Eq.trans (d-zx i₂ i₂ i₃ i₂≢i₃) (Eq.cong₂ (λ a b → rev (dZX {m} a a b)) toℕ-i₂ toℕ-i₃))

------------------------------------------------------------------------
-- (40)

e40 : (d ʷ) (zzℕ {N} 3 4 • hhℕ 0 1 3 2) ≈ (d ʷ) (hhℕ {N} 0 1 3 2 • zzℕ 3 4 • zxℕ 2 2 3)
e40 = begin
  (d ʷ) (zzℕ 3 4 • hhℕ 0 1 3 2)                          ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-zz34 d-hh0132) ⟩
  rev (gadget • dZZ 3 4)                                 ≈⟨ rev-cong unrev ⟩
  rev (dZX 2 2 3 • dZZ 3 4 • gadget)                     ≈⟨ assoc ⟩
  rev gadget • rev (dZZ 3 4) • rev (dZX 2 2 3)           ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-hh0132 (Eq.cong₂ _•_ d-zz34 d-zx223))) ⟩
  (d ʷ) (hhℕ 0 1 3 2 • zzℕ 3 4 • zxℕ 2 2 3) ∎
