------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (39) of Figure 8 (Clément, Appendix E.5)
--
-- (39) is (−1)_[0] (−1)_[1] H_[0,1] H_[3,2] = H_[0,1] H_[3,2] (−1)_[0] (−1)_[1].
-- Decoded, the sign pair is the box on wire 0 with every other control
-- white (the codes of 0 and 1 differ on wire 0 only), and the Hadamard
-- pair is Definition 8.3's gadget, the H gate with its H on wire 0, its
-- box wire 1 and every other control white.  The paper's step is (338)
-- with x = y.  Here the two gates share the negations of the wires 2 …,
-- which are conjugated away (`T`); what is left is the H gate under the
-- swap of the wires 0 1 against the box negated on wire 1, the module's
-- parameter `core` — GeneralN.Box338Eq gives it at every width from five
-- on, from (338) with x = y and X on the H gate's box wire.  The
-- decodings are reversed, which reversal of the commutation absorbs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule39
  {m : ℕ}
  (core : (₃₊ m) ⊢ (Ex ↓ • ΛH (₁₊ m) • Ex ↓) • (X ↑ • Λ□ (₂₊ m) • X ↑)
                  ≈ (X ↑ • Λ□ (₂₊ m) • X ↑) • (Ex ↓ • ΛH (₁₊ m) • Ex ↓))
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (zero ; suc)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X²)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (toBits ; gray ; hd)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (i₀ ; i₁ ; toℕ-i₀ ; toℕ-i₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zzℕ ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; tgtH ; Layout ; negs ; conj₁ ; conj₂)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (d ; dZZ ; gcode ; layout□ ; layoutH ; layoutHFrom ; slot ; gadget)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Easy m using (d-hh0132)

private
  N : ℕ
  N = ₃₊ m

  variable
    k : ℕ

------------------------------------------------------------------------
-- The two layouts

private
  -- The Gray codes of 0 and 1 (as Lemma88.Easy).
  hd-Z : ∀ j → hd (toBits j 0) ≡ false
  hd-Z zero    = Eq.refl
  hd-Z (suc j) = Eq.refl

  gray-Z : ∀ j → gray (toBits j 0) ≡ toBits j 0
  gray-Z zero    = Eq.refl
  gray-Z (suc j) = Eq.cong₂ _∷_ (hd-Z j) (gray-Z j)

  t : Bits m
  t = toBits m 0

  g0 : gcode {m} 0 ≡ false ∷ false ∷ false ∷ t
  g0 = Eq.cong₂ (λ h z → false ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

  g1 : gcode {m} 1 ≡ true ∷ false ∷ false ∷ t
  g1 = Eq.cong₂ (λ h z → true ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

  -- The box: the target on wire 0, white controls elsewhere.
  L₀ : Layout N
  L₀ = tgt ∷ ctrl false ∷ ctrl false ∷ zipWith slot t t

  lay0 : layout□ {m} 0 ≡ L₀
  lay0 = Eq.cong₂ (zipWith slot) g0 g1

  -- The gadget: the H on wire 0, the box on wire 1, white controls.
  LH : Layout N
  LH = tgtH ∷ tgt ∷ ctrl false ∷ layoutHFrom 3 0 1 t

  layH : layoutH {m} (gcode 0) 0 1 ≡ LH
  layH = Eq.cong (λ g → layoutH {m} g 0 1) g0

  -- On the wires 3 … both are the controls of the bits of t.
  negs-tail : ∀ (s : Bits k) w → negs (zipWith slot s s) ≡ negs (layoutHFrom (₃₊ w) 0 1 s)
  negs-tail []          w = Eq.refl
  negs-tail (true ∷ s)  w = Eq.cong _↑ (negs-tail s (suc w))
  negs-tail (false ∷ s) w = Eq.cong (λ z → X • z ↑) (negs-tail s (suc w))

  -- The negations of a layout are an involution.
  negs² : ∀ (L : Layout k) → k ⊢ negs L • negs L ≈ ε
  negs² {k} [] = left-unit
    where open Tools (k VRel,_===_)
  negs² {suc k} (ctrl false ∷ L) = begin
    (X • negs L ↑) • (X • negs L ↑)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    X • (negs L ↑ • X) • negs L ↑       ≈⟨ back _ (front _ (sym (X-↑ (negs L)))) ⟩
    X • (X • negs L ↑) • negs L ↑       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (X • X) • (negs L ↑ • negs L ↑)     ≈⟨ trans (front _ X²) left-unit ⟩
    negs L ↑ • negs L ↑                 ≈⟨ lemma-cong↑ (negs L • negs L) ε (negs² L) ⟩
    ε ∎
    where open Tools ((₁₊ k) VRel,_===_)
  negs² {suc k} (ctrl true ∷ L) = lemma-cong↑ (negs L • negs L) ε (negs² L)
    where open Tools ((₁₊ k) VRel,_===_)
  negs² {suc k} (tgt ∷ L)       = lemma-cong↑ (negs L • negs L) ε (negs² L)
    where open Tools ((₁₊ k) VRel,_===_)
  negs² {suc k} (tgtH ∷ L)      = lemma-cong↑ (negs L • negs L) ε (negs² L)
    where open Tools ((₁₊ k) VRel,_===_)

------------------------------------------------------------------------
-- The two gates, conjugated by the common negations

open Tools (N VRel,_===_)

private
  NY : Circuit m
  NY = negs (layoutHFrom 3 0 1 t)

  -- X on the wires 2 … where t is white.
  T : Circuit N
  T = negs LH

  T² : T • T ≈ ε
  T² = negs² LH

  module CT = Conj T T²

  X₁T : X ↑ • T ≈ T • X ↑
  X₁T = begin
    X ↑ • X ↑ ↑ • NY ↑ ↑ ↑        ≈⟨ trans (sym assoc) (front _ (lemma-cong↑ _ _ (X-↑ X))) ⟩
    (X ↑ ↑ • X ↑) • NY ↑ ↑ ↑      ≈⟨ trans assoc (back _ (lemma-cong↑ _ _ (X-↑ (NY ↑)))) ⟩
    X ↑ ↑ • NY ↑ ↑ ↑ • X ↑        ≈⟨ sym assoc ⟩
    (X ↑ ↑ • NY ↑ ↑ ↑) • X ↑ ∎

  Λ S X₁Λ : Circuit N
  Λ   = Λ□ (₂₊ m)
  S   = Ex ↓ • ΛH (₁₊ m) • Ex ↓
  X₁Λ = X ↑ • Λ • X ↑

  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  negs-L₀ : negs L₀ ≡ X ↑ • T
  negs-L₀ = Eq.cong (λ z → X ↑ • X ↑ ↑ • z ↑ ↑ ↑) (negs-tail t 0)

  -- The decoded sign pair: the box between the negations, X on wire 1
  -- among them.
  box-≡ : dZZ {m} 0 1 ≡ ((X ↑ • T) • ε • Λ • ε • (X ↑ • T)) • ε
  box-≡ = Eq.trans (Eq.cong (λ L → conj₁ L Λ • ε) lay0) (Eq.cong (λ z → (z • ε • Λ • ε • z) • ε) negs-L₀)

  box-form : dZZ {m} 0 1 ≈ CT.⟪ X₁Λ ⟫
  box-form = begin
    dZZ 0 1                                          ≈⟨ ≡→≈ box-≡ ⟩
    ((X ↑ • T) • ε • Λ • ε • (X ↑ • T)) • ε          ≈⟨ right-unit ⟩
    (X ↑ • T) • ε • Λ • ε • (X ↑ • T)                ≈⟨ back _ (trans left-unit (back _ left-unit)) ⟩
    (X ↑ • T) • Λ • (X ↑ • T)                        ≈⟨ front _ X₁T ⟩
    (T • X ↑) • Λ • (X ↑ • T)                        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    T • (X ↑ • Λ • X ↑) • T ∎

  -- The gadget: the H gate under the swap of the wires 0 1, between the
  -- negations.
  gadget-≡ : gadget {m} ≡ T • (Ex • ε) • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T
  gadget-≡ = Eq.cong (λ L → conj₂ L (ΛH (₁₊ m))) layH

  gadget-form : gadget {m} ≈ CT.⟪ S ⟫
  gadget-form = begin
    gadget                                              ≈⟨ ≡→≈ gadget-≡ ⟩
    T • (Ex • ε) • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T     ≈⟨ back _ (front _ right-unit) ⟩
    T • Ex • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T           ≈⟨ back _ (back _ left-unit) ⟩
    T • Ex • ΛH (₁₊ m) • ε • (ε • Ex) • T               ≈⟨ back _ (back _ (back _ left-unit)) ⟩
    T • Ex • ΛH (₁₊ m) • (ε • Ex) • T                   ≈⟨ back _ (back _ (back _ (front _ left-unit))) ⟩
    T • Ex • ΛH (₁₊ m) • Ex • T                         ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    T • (Ex • ΛH (₁₊ m) • Ex) • T ∎

  -- The two commute.
  commute : gadget {m} • dZZ {m} 0 1 ≈ dZZ {m} 0 1 • gadget {m}
  commute = begin
    gadget • dZZ 0 1                ≈⟨ cong gadget-form box-form ⟩
    CT.⟪ S ⟫ • CT.⟪ X₁Λ ⟫           ≈⟨ CT.⟪⟫-≈ core (CT.⟪⟫-• S X₁Λ) (CT.⟪⟫-• X₁Λ S) ⟩
    CT.⟪ X₁Λ ⟫ • CT.⟪ S ⟫           ≈⟨ sym (cong box-form gadget-form) ⟩
    dZZ 0 1 • gadget ∎

  -- The sign pair on 0 1 decodes to its chain of one box.
  d-zz01 : (d ʷ) (zzℕ {N} 0 1) ≡ rev (dZZ {m} 0 1)
  d-zz01 = Eq.trans (Eq.cong (d ʷ) (Eq.trans (Eq.cong₂ zzℕ (Eq.sym toℕ-i₀) (Eq.sym toℕ-i₁)) (zzℕ-zz i₀ i₁)))
                    (Eq.cong₂ (λ a b → rev (dZZ {m} a b)) toℕ-i₀ toℕ-i₁)

------------------------------------------------------------------------
-- (39)

e39 : (d ʷ) (zzℕ {N} 0 1 • hhℕ 0 1 3 2) ≈ (d ʷ) (hhℕ {N} 0 1 3 2 • zzℕ 0 1)
e39 = begin
  (d ʷ) (zzℕ 0 1 • hhℕ 0 1 3 2)          ≈⟨ ≡→≈ (Eq.cong₂ _•_ d-zz01 d-hh0132) ⟩
  rev (gadget • dZZ 0 1)                 ≈⟨ rev-cong commute ⟩
  rev (dZZ 0 1 • gadget)                 ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ d-hh0132 d-zz01)) ⟩
  (d ʷ) (hhℕ 0 1 3 2 • zzℕ 0 1) ∎
