------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (44) of Figure 8 (Clément, Appendix E.5)
--
-- (44) is X_[0,3] X_[1,2] · H_[0,1] H_[3,2] = H_[0,1] H_[3,2] · X_[0,3] X_[1,2].
-- Decoded, H_[0,1] H_[3,2] is the gadget, the H gate on wire 1 with its
-- box wire on wire 0 (Layout.gadget-form).  X_[0,3] X_[1,2] is
-- (−1)_[3] X_[1,2] · (−1)_[0] X_[0,3] (Definition 8.3), eight gates in
-- all: rotations and boxes for the Gray-code pairs 0 1, 1 2 and 2 3,
-- whose layouts put the target on wire 0 or 1 (`lay0`, `lay1`, `lay2`).
-- They all share the negations of the wires 2 … (Layout's `T`), which are
-- conjugated away.  What is left is the module's parameter `core`, which
-- GeneralN.Canon44 gives at every width from five on.  The decodings
-- are reversed, and reversal is a congruence (`rev-cong`).
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

open import Data.Bool using (true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃ ; i₀≢i₃ ; i₁≢i₂ ; xx0312≡)
open import Examples.Groups.Real-Clifford+CH.Encoding using (xxℕ ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Layout ; negs ; tgtWire ; conj₁ ; mc□ ; mc±XZ ; mc±ZX)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dXX ; dZXlo₁ ; dZXhi₁ ; dZZ₁ ; βof ; gadget)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (xx-letter ; d-hh0132)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m}
  using (t ; g0 ; g1 ; g2 ; L₀ ; L₁ ; L₂ ; lay0 ; lay1 ; lay2 ; negs-tail ; NY ; T ; module CT ; S ; gadget-form)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  Λ XB ZXB B₁ Yb XW XWi : Circuit N
  Λ   = Λ□ (₂₊ m)
  XB  = ΛXZ (₂₊ m)
  ZXB = ΛZX (₂₊ m)
  B₁  = Ex ↓ • Λ • Ex ↓
  Yb  = Ex ↓ • XB • Ex ↓
  XW  = X ↑ • XB • X ↑
  XWi = X ↑ • ZXB • X ↑

  -- The decoded X_[0,3] X_[1,2], between the negations.
  Cc : Circuit N
  Cc = (Yb • B₁ • Λ) • (XW • (XB • Yb • ZXB) • XWi)

  ------------------------------------------------------------------------
  -- The decoded X_[0,3] X_[1,2]

  cong-dXX : ∀ {a a′ b b′ c c′ e e′ : ℕ} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → dXX {m} a b c e ≡ dXX a′ b′ c′ e′
  cong-dXX Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

  d-xx : (d ʷ) (xxℕ {N} 0 3 1 2) ≡ rev (dXX {m} 0 3 1 2)
  d-xx = Eq.trans (Eq.cong (d ʷ) (Eq.trans xx0312≡ (xx-letter i₀ i₃ i₁ i₂ i₀≢i₃ i₁≢i₂)))
                  (Eq.cong rev (cong-dXX toℕ-i₀ toℕ-i₃ toℕ-i₁ toℕ-i₂))

  -- The targets' bits.
  βof-0 : βof {m} 0 ≡ false
  βof-0 = Eq.cong₂ (λ L g → lookupℕ (tgtWire L) g) lay0 g0

  βof-1 : βof {m} 1 ≡ false
  βof-1 = Eq.cong₂ (λ L g → lookupℕ (tgtWire L) g) lay1 g1

  βof-2 : βof {m} 2 ≡ true
  βof-2 = Eq.cong₂ (λ L g → lookupℕ (tgtWire L) g) lay2 g2

  ------------------------------------------------------------------------
  -- Each layout between the negations T

  X₁T : X ↑ • T ≈ T • X ↑
  X₁T = begin
    X ↑ • X ↑ ↑ • NY ↑ ↑ ↑        ≈⟨ trans (sym assoc) (front _ (lemma-cong↑ _ _ (X-↑ X))) ⟩
    (X ↑ ↑ • X ↑) • NY ↑ ↑ ↑      ≈⟨ trans assoc (back _ (lemma-cong↑ _ _ (X-↑ (NY ↑)))) ⟩
    X ↑ ↑ • NY ↑ ↑ ↑ • X ↑        ≈⟨ sym assoc ⟩
    (X ↑ ↑ • NY ↑ ↑ ↑) • X ↑ ∎

  negs-L₀ : negs L₀ ≡ X ↑ • T
  negs-L₀ = Eq.cong (λ z → X ↑ • X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  negs-L₁ : negs L₁ ≡ T
  negs-L₁ = Eq.cong (λ z → X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  negs-L₂ : negs L₂ ≡ T
  negs-L₂ = Eq.cong (λ z → X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  form₀ : ∀ g → conj₁ L₀ g ≈ CT.⟪ X ↑ • g • X ↑ ⟫
  form₀ g = begin
    conj₁ L₀ g                                ≈⟨ ≡→≈ (Eq.cong (λ z → z • ε • g • ε • z) negs-L₀) ⟩
    (X ↑ • T) • ε • g • ε • (X ↑ • T)         ≈⟨ back _ (trans left-unit (back _ left-unit)) ⟩
    (X ↑ • T) • g • (X ↑ • T)                 ≈⟨ front _ X₁T ⟩
    (T • X ↑) • g • (X ↑ • T)                 ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    T • (X ↑ • g • X ↑) • T ∎

  form₁ : ∀ g → conj₁ L₁ g ≈ CT.⟪ Ex • g • Ex ⟫
  form₁ g = begin
    conj₁ L₁ g                                ≈⟨ ≡→≈ (Eq.cong (λ z → z • (Ex • ε) • g • (ε • Ex) • z) negs-L₁) ⟩
    T • (Ex • ε) • g • (ε • Ex) • T           ≈⟨ back _ (cong right-unit (back _ (front _ left-unit))) ⟩
    T • Ex • g • Ex • T                       ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    T • (Ex • g • Ex) • T ∎

  form₂ : ∀ g → conj₁ L₂ g ≈ CT.⟪ g ⟫
  form₂ g = trans (≡→≈ (Eq.cong (λ z → z • ε • g • ε • z) negs-L₂)) (back _ (trans left-unit (back _ left-unit)))

  -- The eight letters.
  l1 : dZXlo₁ {m} 1 ≈ CT.⟪ Yb ⟫
  l1 = trans (≡→≈ (Eq.cong₂ mc±XZ βof-1 lay1)) (form₁ XB)

  z1 : dZZ₁ {m} 1 ≈ CT.⟪ B₁ ⟫
  z1 = trans (≡→≈ (Eq.cong mc□ lay1)) (form₁ Λ)

  z2 : dZZ₁ {m} 2 ≈ CT.⟪ Λ ⟫
  z2 = trans (≡→≈ (Eq.cong mc□ lay2)) (form₂ Λ)

  l0 : dZXlo₁ {m} 0 ≈ CT.⟪ XW ⟫
  l0 = trans (≡→≈ (Eq.cong₂ mc±XZ βof-0 lay0)) (form₀ XB)

  h2 : dZXhi₁ {m} 2 ≈ CT.⟪ XB ⟫
  h2 = trans (≡→≈ (Eq.cong₂ mc±ZX βof-2 lay2)) (form₂ XB)

  l2 : dZXlo₁ {m} 2 ≈ CT.⟪ ZXB ⟫
  l2 = trans (≡→≈ (Eq.cong₂ mc±XZ βof-2 lay2)) (form₂ ZXB)

  h0 : dZXhi₁ {m} 0 ≈ CT.⟪ XWi ⟫
  h0 = trans (≡→≈ (Eq.cong₂ mc±ZX βof-0 lay0)) (form₀ ZXB)

  -- (−1)_[3] X_[1,2] is the rotation for 1, 2 and the boxes for 1, 2 and
  -- 2, 3; (−1)_[0] X_[0,3] the rotations for 0, 1, 2, 1 and 2, then 0.
  xx-form : dXX {m} 0 3 1 2 ≈ CT.⟪ Cc ⟫
  xx-form = begin
    (dZXlo₁ 1 • dZZ₁ 1 • dZZ₁ 2 • ε) • dZXlo₁ 0 • (dZXhi₁ 2 • dZXlo₁ 1 • dZXlo₁ 2) • dZXhi₁ 0
      ≈⟨ cong (cong l1 (cong z1 (trans right-unit z2))) (cong l0 (cong (cong h2 (cong l1 l2)) h0)) ⟩
    (CT.⟪ Yb ⟫ • CT.⟪ B₁ ⟫ • CT.⟪ Λ ⟫) • CT.⟪ XW ⟫ • (CT.⟪ XB ⟫ • CT.⟪ Yb ⟫ • CT.⟪ ZXB ⟫) • CT.⟪ XWi ⟫
      ≈⟨ sym (CT.⟪⟫-•₂ (CT.⟪⟫-•₃ refl refl refl) (CT.⟪⟫-•₃ refl (CT.⟪⟫-•₃ refl refl refl) refl)) ⟩
    CT.⟪ Cc ⟫ ∎

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
