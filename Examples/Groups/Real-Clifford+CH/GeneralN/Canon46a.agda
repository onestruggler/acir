------------------------------------------------------------------------
-- Presentations of groups
--
-- Rule (46) of Figure 8 at the canonical position, reduced to one
-- commutation (Clément, Lemma 8.8)
--
-- At width 5 + k the six gates of Lemma88.Letters46 are A (the H gate
-- ΛH white on wire 2), B (it under the swap of the wires 1 2), Zg (the
-- box white on wire 2), D, C and F (the H gate with its H on wire 0 and
-- its box wire on wire 1, resp. 2 — black on wire 2, resp. 1 — and F
-- white on wire 1).  All are involutions, and Core46 says the word
-- A B Zg D C B A F is one:
--
--   * Zg, D and C commute pairwise (`ZDC`): (338) with x ≠ y and x = y
--     under X and the swaps, and for D, C under P ⊗ P and the swap of the
--     wires 0 1, which carries D to the box and fixes C;
--   * so Core46 is [A F A, B X B] with X = Zg D C (`reduce`);
--   * X = Y K₁ K₂, Y the box negated on wire 1, K₁ = Yo D and K₂ = Zo C
--     with Yo and Zo the box with wire 0 idle on wire 1, resp. 2 — the
--     merges (309);
--   * Y passes B ((337) under X on wire 2 and the swap of the wires 1 2),
--     A (Y is the box times Yo, which P ⊗ P on the wires 0 1 fixes (276)
--     and carries A to Zg) and F ((338) under the swap and X);
--   * the D-trick twice: UA, the CH from wire 2 negated onto wire 1, is
--     A over every colouring of the wires 3 … (merge-top₂), and every
--     colouring but the black one passes F: between P ⊗ P on the wires
--     0 1 it is Zg and F is the H gate Vh times the box Fo with wire 1
--     idle, which pass it by (339) (Canon40's `eq339c`, under the cycle
--     of the wires 0 1 2) and (336); so A F A = UA F UA (`AFA`).  UB, the
--     CH from wire 1 onto wire 2, is B over every colouring, and every
--     other colouring passes K₁ K₂, letter by letter, by (339) and (335),
--     (336), directly or between P ⊗ P on the wires 0 2; so
--     B K B = UB K UB (`BKB`).
--
-- What is left is the commutation of UA F UA and UB K₁ K₂ UB, the
-- module parameter of `reduce` (GeneralN.Canon46b).  Every identity was
-- checked numerically at five wires first (scratchpad t46agda.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon46a
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; ≤-refl)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X² ; CH²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (col-pair ; col-pair′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swap-braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (box276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (∏-conj ; ∏-cong ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry ; sep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box337 complete₂ complete₃ using (eq337 ; col-2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (pass-last ; eq339c)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46
  using (h0312 ; h3425 ; z23 ; h7645 ; h3245 ; h0176 ; Core46)

------------------------------------------------------------------------
-- At width 5 + k

module At (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m : ℕ
    N = ₁₊ (₄₊ k)
    m = ₂₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open XY k below using (eq338xy ; X-Hg ; S-ΛH)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₂)

  ----------------------------------------------------------------------
  -- The gates

  -- The box on wire 0, 1 or 2, the H gate on wire 1 with its box wire 0
  -- (ΛH), and Col's H gate on wire 0 with its box wire 1.
  Λ₀ Λ₁ Λ₂ LH HG : Circuit N
  Λ₀ = Λ□ (₄₊ k)
  Λ₁ = Ex ↓ • Λ₀ • Ex ↓
  Λ₂ = Ex ↑ • Λ₁ • Ex ↑
  LH = ΛH (₃₊ k)
  HG = Hg (₂₊ k)

  -- The six letters.
  A B Zg D C F : Circuit N
  A  = h0312 {m}
  B  = h3425 {m}
  Zg = z23 {m}
  D  = h7645 {m}
  C  = h3245 {m}
  F  = h0176 {m}

  -- The box negated on wire 1; the box with wire 0 idle, on wire 1 or 2;
  -- and the box on wire 2 with wire 1 idle.
  Y Yo Zo Fo : Circuit N
  Y  = X ↑ • Λ₀ • X ↑
  Yo = Λ□ (₃₊ k) ↑
  Zo = Ex ↑ • Yo • Ex ↑
  Fo = Ex ↓ • Zo • Ex ↓

  -- The box on wire 2 negated on wire 1, on wire 1 or 2 negated on wire
  -- 0, and the H gates on wire 1 (resp. 2) with their box wires on wire
  -- 2 (resp. 1).
  f C0 D0 Vh Hd : Circuit N
  f  = X ↑ • Λ₂ • X ↑
  C0 = X • Λ₁ • X
  D0 = X • Λ₂ • X
  Vh = PP ↑ • Λ₂ • PP ↑
  Hd = PP ↑ • Λ₁ • PP ↑

  -- The CH from wire 2, negated, onto wire 1, and from wire 1 onto
  -- wire 2; P ⊗ P on the wires 0 2.
  UA UB PP₀₂ : Circuit N
  UA   = X ↑ ↑ • CH ↑ • X ↑ ↑
  UB   = Ex ↑ • CH ↑ • Ex ↑
  PP₀₂ = Ex ↑ • PP ↓ • Ex ↑

  K₁ K₂ : Circuit N
  K₁ = Yo • D
  K₂ = Zo • C

  -- The colouring of the wires 3 ….
  Nc : Bits m → Circuit N
  Nc c = negsB c ↑ ↑ ↑

  ----------------------------------------------------------------------
  -- Tools

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    via′ : ∀ {y u w : Circuit N} → u ≈ w → w • y ≈ y • w → u • y ≈ y • u
    via′ e p = trans (front _ e) (trans p (back _ (sym e)))

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p′ • q′ ≈ q′ • p′ → p • q ≈ q • p
    both ep eq e = trans (cong ep eq) (trans e (sym (cong eq ep)))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    pass₂′ : ∀ {a u v : Circuit N} → u • a ≈ a • u → v • a ≈ a • v → (u • v) • a ≈ a • (u • v)
    pass₂′ eu ev = sym (pass₂ (sym eu) (sym ev))

    pass₃ : ∀ {a u v w : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • w ≈ w • a →
            a • (u • v • w) ≈ (u • v • w) • a
    pass₃ eu ev ew = pass₂ eu (pass₂ ev ew)

  Ex↑² : Ex ↑ • Ex ↑ ≈ ε
  Ex↑² = lemma-cong↑ _ _ Ex²

  X↑² : X ↑ • X ↑ ≈ ε
  X↑² = lemma-cong↑ _ _ X²

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

  τ² : τ₀₂ • τ₀₂ ≈ ε
  τ² = conj-invol Ex² Ex↑²

  Q² : PP₀₂ • PP₀₂ ≈ ε
  Q² = S₁₂.⟪⟫-invol eq111

  Nc² : ∀ c → Nc c • Nc c ≈ ε
  Nc² c = negs² (true ∷ true ∷ true ∷ c)

  module P  = Conj {N} (PP ↓) eq111
  module N₂ = Conj {N} (X ↑ ↑) X₂²
  module X₁ = Conj {N} (X ↑) X↑²
  module T  = Conj {N} τ₀₂ τ²
  module Q  = Conj {N} PP₀₂ Q²
  module Pu = Conj {N} (PP ↑) (lemma-cong↑ _ _ eq111)

  private
    module CP  = Carry {N} (PP ↓) eq111
    module CN  = Carry {N} (X ↑ ↑) X₂²
    module CX₁ = Carry {N} (X ↑) X↑²
    module C01 = Carry {N} (Ex ↓) Ex²
    module C12 = Carry {N} (Ex ↑) Ex↑²
    module CT  = Carry {N} τ₀₂ τ²
    module CQ  = Carry {N} PP₀₂ Q²
    module CNc (c : Bits m) = Carry {N} (Nc c) (Nc² c)

  -- The cycle of the wires 0 1 2 (0 → 2 → 1 → 0), and its inverse.
  πc π2c : Circuit N → Circuit N
  πc  w = S₁₂.⟪ S₀₁.⟪ w ⟫ ⟫
  π2c w = S₀₁.⟪ S₁₂.⟪ w ⟫ ⟫

  πc-•₃ : ∀ {a b d a′ b′ d′} → πc a ≈ a′ → πc b ≈ b′ → πc d ≈ d′ → πc (a • b • d) ≈ a′ • b′ • d′
  πc-•₃ ea eb ed = trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-•₃ refl refl refl)) (S₁₂.⟪⟫-•₃ ea eb ed)

  π2c-•₃ : ∀ {a b d a′ b′ d′} → π2c a ≈ a′ → π2c b ≈ b′ → π2c d ≈ d′ → π2c (a • b • d) ≈ a′ • b′ • d′
  π2c-•₃ ea eb ed = trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-•₃ refl refl refl)) (S₀₁.⟪⟫-•₃ ea eb ed)

  -- A commutation after a conjugation is one before it.
  π-back : ∀ {a b a′ b′} → πc a ≈ a′ → πc b ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  π-back {a} {b} ea eb e =
    C01.carry (S₀₁.⟪⟫-⟪⟫ a) (S₀₁.⟪⟫-⟪⟫ b)
      (C12.carry (S₁₂.⟪⟫-⟪⟫ (S₀₁.⟪ a ⟫)) (S₁₂.⟪⟫-⟪⟫ (S₀₁.⟪ b ⟫)) (both ea eb e))

  π2-back : ∀ {a b a′ b′} → π2c a ≈ a′ → π2c b ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  π2-back {a} {b} ea eb e =
    C12.carry (S₁₂.⟪⟫-⟪⟫ a) (S₁₂.⟪⟫-⟪⟫ b)
      (C01.carry (S₀₁.⟪⟫-⟪⟫ (S₁₂.⟪ a ⟫)) (S₀₁.⟪⟫-⟪⟫ (S₁₂.⟪ b ⟫)) (both ea eb e))

  τ-back : ∀ {a b a′ b′} → T.⟪ a ⟫ ≈ a′ → T.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  τ-back ea eb e = CT.carry (conj-sym τ² ea) (conj-sym τ² eb) e

  Q-back : ∀ {a b a′ b′} → Q.⟪ a ⟫ ≈ a′ → Q.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  Q-back ea eb e = CQ.carry (conj-sym Q² ea) (conj-sym Q² eb) e

  P-back : ∀ {a b a′ b′} → P.⟪ a ⟫ ≈ a′ → P.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  P-back ea eb e = CP.carry (conj-sym eq111 ea) (conj-sym eq111 eb) e

  S12-back : ∀ {a b a′ b′} → S₁₂.⟪ a ⟫ ≈ a′ → S₁₂.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  S12-back ea eb e = C12.carry (conj-sym Ex↑² ea) (conj-sym Ex↑² eb) e

  S01-back : ∀ {a b a′ b′} → S₀₁.⟪ a ⟫ ≈ a′ → S₀₁.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  S01-back ea eb e = C01.carry (conj-sym Ex² ea) (conj-sym Ex² eb) e

  N2-back : ∀ {a b a′ b′} → N₂.⟪ a ⟫ ≈ a′ → N₂.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  N2-back ea eb e = CN.carry (conj-sym X₂² ea) (conj-sym X₂² eb) e

  X1-back : ∀ {a b a′ b′} → X₁.⟪ a ⟫ ≈ a′ → X₁.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
  X1-back ea eb e = CX₁.carry (conj-sym X↑² ea) (conj-sym X↑² eb) e

  ----------------------------------------------------------------------
  -- Relabelling the letters

  Λ₀² : Λ₀ • Λ₀ ≈ ε
  Λ₀² = Canon.invol canon

  Λ₁² : Λ₁ • Λ₁ ≈ ε
  Λ₁² = S₀₁.⟪⟫-invol Λ₀²

  Λ₂² : Λ₂ • Λ₂ ≈ ε
  Λ₂² = S₁₂.⟪⟫-invol Λ₁²

  S₁₂-Λ₀ : S₁₂.⟪ Λ₀ ⟫ ≈ Λ₀
  S₁₂-Λ₀ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ Ex↑²) right-unit)))

  S12X1 : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
  S12X1 = X-step 1 (s≤s (s≤s z≤n))

  S12X2 : S₁₂.⟪ X ↑ ↑ ⟫ ≈ X ↑
  S12X2 = conj-sym Ex↑² S12X1

  S01X0 : S₀₁.⟪ X ⟫ ≈ X ↑
  S01X0 = X-step 0 (s≤s z≤n)

  S01X1 : S₀₁.⟪ X ↑ ⟫ ≈ X
  S01X1 = conj-sym Ex² S01X0

  S12X0 : S₁₂.⟪ X ⟫ ≈ X
  S12X0 = trans (back _ (X-↑ Ex)) (trans (sym assoc) (trans (front _ Ex↑²) left-unit))

  S01X2 : S₀₁.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
  S01X2 = trans (back _ (sym (low-comm Ex X))) (trans (sym assoc) (trans (front _ Ex²) left-unit))

  private
    br : Ex ↓ • Ex ↑ • Ex ↓ ≈ Ex ↑ • Ex ↓ • Ex ↑
    br = swap-braid 0 (s≤s (s≤s (s≤s z≤n)))

    -- Ex (Ex↑ (Ex w Ex) Ex↑) Ex is Ex↑ (Ex w Ex) Ex↑ under the braid
    -- relation, and w passes Ex↑ when it is the box.
    cancel-mid : ∀ (w : Circuit N) → Ex • Ex ↑ • (Ex • Ex) • w • (Ex • Ex) • Ex ↑ • Ex ≈ Ex • Ex ↑ • w • Ex ↑ • Ex
    cancel-mid w = back _ (back _ (trans (front _ Ex²) (trans left-unit (back _ (trans (front _ Ex²) left-unit)))))

  -- τ₀₂ carries the box on wire 0 to wire 2 and fixes the box on wire 1.
  τΛ₀ : T.⟪ Λ₀ ⟫ ≈ Λ₂
  τΛ₀ = begin
    (Ex • Ex ↑ • Ex) • Λ₀ • (Ex • Ex ↑ • Ex)
      ≈⟨ cong br (back _ br) ⟩
    (Ex ↑ • Ex • Ex ↑) • Λ₀ • (Ex ↑ • Ex • Ex ↑)
      ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    Ex ↑ • (Ex • S₁₂.⟪ Λ₀ ⟫ • Ex) • Ex ↑
      ≈⟨ mid _ _ (mid _ _ S₁₂-Λ₀) ⟩
    Λ₂ ∎

  τΛ₂ : T.⟪ Λ₂ ⟫ ≈ Λ₀
  τΛ₂ = conj-sym τ² τΛ₀

  τΛ₁ : T.⟪ Λ₁ ⟫ ≈ Λ₁
  τΛ₁ = begin
    (Ex • Ex ↑ • Ex) • (Ex • Λ₀ • Ex) • (Ex • Ex ↑ • Ex)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
    Ex • Ex ↑ • (Ex • Ex) • Λ₀ • (Ex • Ex) • Ex ↑ • Ex
      ≈⟨ cancel-mid Λ₀ ⟩
    Ex • Ex ↑ • Λ₀ • Ex ↑ • Ex
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex • S₁₂.⟪ Λ₀ ⟫ • Ex
      ≈⟨ mid _ _ S₁₂-Λ₀ ⟩
    Λ₁ ∎

  -- The cycle carries the box on wire 0 to wire 2 (by definition), on
  -- wire 1 to wire 0 and on wire 2 to wire 1.
  πΛ₁ : πc Λ₁ ≈ Λ₀
  πΛ₁ = trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ Λ₀)) S₁₂-Λ₀

  πΛ₂ : πc Λ₂ ≈ Λ₁
  πΛ₂ = begin
    Ex ↑ • (Ex • (Ex ↑ • (Ex • Λ₀ • Ex) • Ex ↑) • Ex) • Ex ↑
      ≈⟨ by-passoc (□ • (□ • (□ • (□ • □ • □) • □) • □) • □) ((□ • □ • □) • □ • □ • □ • (□ • □ • □)) Eq.refl ⟩
    (Ex ↑ • Ex • Ex ↑) • Ex • Λ₀ • Ex • (Ex ↑ • Ex • Ex ↑)
      ≈⟨ cong (sym br) (back _ (back _ (back _ (sym br)))) ⟩
    (Ex • Ex ↑ • Ex) • Ex • Λ₀ • Ex • (Ex • Ex ↑ • Ex)
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □ • (□ • □ • □)) (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
    Ex • Ex ↑ • (Ex • Ex) • Λ₀ • (Ex • Ex) • Ex ↑ • Ex
      ≈⟨ cancel-mid Λ₀ ⟩
    Ex • Ex ↑ • Λ₀ • Ex ↑ • Ex
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex • S₁₂.⟪ Λ₀ ⟫ • Ex
      ≈⟨ mid _ _ S₁₂-Λ₀ ⟩
    Λ₁ ∎

  π2Λ₁ : π2c Λ₁ ≈ Λ₂
  π2Λ₁ = trans (by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl) τΛ₀

  -- The one-wire and two-wire gates, relabelled.
  πX0 : πc X ≈ X ↑ ↑
  πX0 = trans (S₁₂.⟪⟫-cong S01X0) S12X1

  πX2 : πc (X ↑ ↑) ≈ X ↑
  πX2 = trans (S₁₂.⟪⟫-cong S01X2) S12X2

  π2X0 : π2c X ≈ X ↑
  π2X0 = trans (S₀₁.⟪⟫-cong S12X0) S01X0

  πPPu : πc (PP ↑) ≈ PP ↓
  πPPu = L₃-sem (Ex ↑ • (Ex • PP ↑ • Ex) • Ex ↑) PP Eq.refl

  τX0 : T.⟪ X ⟫ ≈ X ↑ ↑
  τX0 = L₃-sem (τ₀₂ • X • τ₀₂) (X ↑ ↑) Eq.refl

  τX1 : T.⟪ X ↑ ⟫ ≈ X ↑
  τX1 = L₃-sem (τ₀₂ • X ↑ • τ₀₂) (X ↑) Eq.refl

  τPPu : T.⟪ PP ↑ ⟫ ≈ PP ↓
  τPPu = L₃-sem (τ₀₂ • PP ↑ • τ₀₂) PP Eq.refl

  klein₁ : PP₀₂ • PP ↓ ≈ PP ↑
  klein₁ = L₃-sem ((Ex ↑ • PP • Ex ↑) • PP) (PP ↑) Eq.refl

  klein₂ : PP ↓ • PP₀₂ ≈ PP ↑
  klein₂ = L₃-sem (PP • (Ex ↑ • PP • Ex ↑)) (PP ↑) Eq.refl

  SSPP : π2c (PP ↓) ≈ PP ↑
  SSPP = L₃-sem (Ex • (Ex ↑ • PP • Ex ↑) • Ex) (PP ↑) Eq.refl

  X1Q : X ↑ • PP₀₂ ≈ PP₀₂ • X ↑
  X1Q = L₃-sem (X ↑ • (Ex ↑ • PP • Ex ↑)) ((Ex ↑ • PP • Ex ↑) • X ↑) Eq.refl

  PX2 : PP ↓ • X ↑ ↑ ≈ X ↑ ↑ • PP ↓
  PX2 = low-comm PP X

  -- The colourings of the wires 3 … pass everything on the wires 0 1 2.
  loc : ∀ (u : Circuit 3) c → (u ↓ᵏ m) • Nc c ≈ Nc c • (u ↓ᵏ m)
  loc u c = local-comm u (negsB c)

  X2-Nc : ∀ c → X ↑ ↑ • Nc c ≈ Nc c • X ↑ ↑
  X2-Nc c = loc (X ↑ ↑) c

  X1-Nc : ∀ c → X ↑ • Nc c ≈ Nc c • X ↑
  X1-Nc c = loc (X ↑) c

  πNc : ∀ c → πc (Nc c) ≈ Nc c
  πNc c = trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-fix (loc Ex c))) (S₁₂.⟪⟫-fix (loc (Ex ↑) c))

  π2Nc : ∀ c → π2c (Nc c) ≈ Nc c
  π2Nc c = trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-fix (loc (Ex ↑) c))) (S₀₁.⟪⟫-fix (loc Ex c))

  τNc : ∀ c → T.⟪ Nc c ⟫ ≈ Nc c
  τNc c = T.⟪⟫-fix (loc τ₀₂ c)

  QNc : ∀ c → Q.⟪ Nc c ⟫ ≈ Nc c
  QNc c = Q.⟪⟫-fix (loc (Ex ↑ • PP • Ex ↑) c)

  -- A colouring of a conjugate.
  col-in : ∀ (u : Circuit 3) c (w : Circuit N) →
           (u ↓ᵏ m) • col (true ∷ true ∷ true ∷ c) w • (u ↓ᵏ m) ≈ col (true ∷ true ∷ true ∷ c) ((u ↓ᵏ m) • w • (u ↓ᵏ m))
  col-in u c w = conj-swap (loc u c) w

  -- P ⊗ P on the wires 0 2 is P ⊗ P on the wires 0 1 between the swaps
  -- of the wires 1 2.
  Qe : ∀ x → Q.⟪ x ⟫ ≈ S₁₂.⟪ P.⟪ S₁₂.⟪ x ⟫ ⟫ ⟫
  Qe x = by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl

  ----------------------------------------------------------------------
  -- The letters: involutions and forms

  D≈HG : D ≈ HG
  D≈HG = S-ΛH

  C≈ : C ≈ S₁₂.⟪ D ⟫
  C≈ = by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl

  A² : A • A ≈ ε
  A² = N₂.⟪⟫-invol (P.⟪⟫-invol Λ₀²)

  B² : B • B ≈ ε
  B² = S₁₂.⟪⟫-invol (P.⟪⟫-invol Λ₀²)

  Y² : Y • Y ≈ ε
  Y² = X₁.⟪⟫-invol Λ₀²

  UA² : UA • UA ≈ ε
  UA² = N₂.⟪⟫-invol (lemma-cong↑ _ _ CH²)

  UB² : UB • UB ≈ ε
  UB² = S₁₂.⟪⟫-invol (lemma-cong↑ _ _ CH²)

  -- Colourings black but for one wire.
  ones₂ : Bits (₂₊ k)
  ones₂ = replicate (₂₊ k) true

  s101 s110 onesN : Bits N
  s101  = true ∷ false ∷ replicate (₃₊ k) true
  s110  = true ∷ true ∷ false ∷ ones₂
  onesN = replicate N true

  -- White on wire 1 and black elsewhere is X on wire 1.
  col-1 : ∀ (w : Circuit N) → col (true ∷ false ∷ replicate (₃₊ k) true) w ≈ X ↑ • w • X ↑
  col-1 w = trans (≡→≈ (Eq.cong (λ z → (X ↑ • z ↑ ↑) • w • (X ↑ • z ↑ ↑)) (allT (₃₊ k))))
                  (cong right-unit (back _ right-unit))

  col-ones : ∀ (w : Circuit N) → col (replicate N true) w ≈ w
  col-ones w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

  -- The colourings of Y and Zg on the wires 3 ….
  colY : ∀ c → col (true ∷ false ∷ true ∷ c) Λ₀ ≈ col (true ∷ true ∷ true ∷ c) Y
  colY c = trans (front _ (X1-Nc c)) (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

  colZ : ∀ c → col (true ∷ true ∷ false ∷ c) Λ₀ ≈ col (true ∷ true ∷ true ∷ c) Zg
  colZ c = trans (front _ (X2-Nc c)) (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

  S₁₂Y : S₁₂.⟪ Y ⟫ ≈ Zg
  S₁₂Y = S₁₂.⟪⟫-•₃ S12X1 S₁₂-Λ₀ S12X1

  S₁₂Zg : S₁₂.⟪ Zg ⟫ ≈ Y
  S₁₂Zg = S₁₂.⟪⟫-•₃ S12X2 S₁₂-Λ₀ S12X2

  PZg : P.⟪ Zg ⟫ ≈ A
  PZg = conj-swap PX2 Λ₀

  ----------------------------------------------------------------------
  -- Boxes commute

  W-Y : Λ₀ • Y ≈ Y • Λ₀
  W-Y = via (sym (col-1 Λ₀)) (eq335 k below s101)

  W-Zg : Λ₀ • Zg ≈ Zg • Λ₀
  W-Zg = via (sym (col-2 Λ₀)) (eq335 k below s110)

  Y-Zg : Y • Zg ≈ Zg • Y
  Y-Zg = both (sym (col-1 Λ₀)) (sym (col-2 Λ₀)) (col-pair s101 s110 Λ₀ (eq335 k below))

  ----------------------------------------------------------------------
  -- Merges (309)

  WY : Λ₀ • Y ≈ Yo
  WY = Canon.merge canon

  YW : Y • Λ₀ ≈ Yo
  YW = trans (sym W-Y) WY

  Yo≈ : Yo ≈ Λ₀ • Y
  Yo≈ = sym WY

  WZ : Λ₀ • Zg ≈ Zo
  WZ = S₁₂.⟪⟫-≈ WY (S₁₂.⟪⟫-•₂ S₁₂-Λ₀ S₁₂Y) refl

  -- Yo on wire 1 is the box on wire 1 and its copy negated on wire 0.
  Yo-form : Yo ≈ C0 • Λ₁
  Yo-form = sym (S₀₁.⟪⟫-≈ YW (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-•₃ S01X1 refl S01X1) refl) (Canon.wire274 canon))

  YYo : Y • Yo ≈ Λ₀
  YYo = begin
    Y • Yo                ≈⟨ back _ Yo≈ ⟩
    Y • (Λ₀ • Y)          ≈⟨ trans (sym assoc) (front _ (sym W-Y)) ⟩
    (Λ₀ • Y) • Y          ≈⟨ trans assoc (trans (back _ Y²) right-unit) ⟩
    Λ₀ ∎

  WZo : Λ₀ • Zo ≈ Zg
  WZo = trans (back _ (sym WZ)) (trans (sym assoc) (trans (front _ Λ₀²) left-unit))

  Yo² : Yo • Yo ≈ ε
  Yo² = begin
    Yo • Yo                     ≈⟨ cong Yo≈ (sym YW) ⟩
    (Λ₀ • Y) • (Y • Λ₀)         ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    Λ₀ • (Y • Y) • Λ₀           ≈⟨ back _ (trans (front _ Y²) left-unit) ⟩
    Λ₀ • Λ₀                     ≈⟨ Λ₀² ⟩
    ε ∎

  -- The box on wire 2 with wire 1 idle is the box on wire 2 and its copy
  -- negated on wire 1: the merge under τ₀₂.
  τYo : T.⟪ Yo ⟫ ≈ Fo
  τYo = begin
    T.⟪ Yo ⟫
      ≈⟨ T.⟪⟫-cong (sym (Canon.wire274 canon)) ⟩
    (Ex • Ex ↑ • Ex) • (Ex • Yo • Ex) • (Ex • Ex ↑ • Ex)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
    Ex • Ex ↑ • (Ex • Ex) • Yo • (Ex • Ex) • Ex ↑ • Ex
      ≈⟨ cancel-mid Yo ⟩
    Ex • Ex ↑ • Yo • Ex ↑ • Ex
      ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Fo ∎

  Fo-form : Λ₂ • f ≈ Fo
  Fo-form = T.⟪⟫-≈ WY (T.⟪⟫-•₂ τΛ₀ (T.⟪⟫-•₃ τX1 τΛ₀ τX1)) τYo

  -- P ⊗ P on the wires 1 2 passes Fo: P ⊗ P on its box wire and its idle
  -- wire (276), under the cycle.
  PuFo : PP ↑ • Fo • PP ↑ ≈ Fo
  PuFo = begin
    PP ↑ • Fo • PP ↑
      ≈⟨ cong (sym SSPP) (back _ (sym SSPP)) ⟩
    π2c (PP ↓) • π2c Yo • π2c (PP ↓)
      ≈⟨ sym (π2c-•₃ refl refl refl) ⟩
    π2c (PP ↓ • Yo • PP ↓)
      ≈⟨ S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (box276 (₁₊ k) c)) ⟩
    Fo ∎

  PYo : P.⟪ Yo ⟫ ≈ Yo
  PYo = box276 (₁₊ k) c

  ----------------------------------------------------------------------
  -- Step 1: Zg, D and C commute pairwise

  W-D : Λ₀ • D ≈ D • Λ₀
  W-D = via D≈HG eq338xy

  X1D : X ↑ • D ≈ D • X ↑
  X1D = via D≈HG X-Hg

  Zg-D : Zg • D ≈ D • Zg
  Zg-D = via D≈HG (CN.carry refl (N₂.⟪⟫-⟪⟫ HG)
                     (trans (back _ (sym (col-2 HG))) (trans (sep k below ones₂) (front _ (col-2 HG)))))

  Y-D : Y • D ≈ D • Y
  Y-D = CX₁.carry refl (X₁.⟪⟫-fix X1D) W-D

  Zg-C : Zg • C ≈ C • Zg
  Zg-C = C12.carry S₁₂Y (sym C≈) Y-D

  W-C : Λ₀ • C ≈ C • Λ₀
  W-C = C12.carry S₁₂-Λ₀ (sym C≈) W-D

  -- P ⊗ P on the wires 0 1 and the swap of the wires 0 1 carry D to the
  -- box and fix C.
  SPC : S₀₁.⟪ P.⟪ C ⟫ ⟫ ≈ C
  SPC = begin
    Ex • (PP • ((Ex ↑ • Ex) • (PP • Λ₀ • PP) • (Ex • Ex ↑)) • PP) • Ex
      ≈⟨ by-passoc (□ • (□ • ((□ • □) • (□ • □ • □) • (□ • □)) • □) • □)
                   ((□ • □ • □ • □ • □) • □ • (□ • □ • □ • □ • □)) Eq.refl ⟩
    (Ex • PP • Ex ↑ • Ex • PP) • Λ₀ • (PP • Ex • Ex ↑ • PP • Ex)
      ≈⟨ cong DC1 (back _ DC2) ⟩
    ((Ex ↑ • Ex • PP) • Ex ↑) • Λ₀ • (Ex ↑ • (PP • Ex • Ex ↑))
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    (Ex ↑ • Ex • PP) • S₁₂.⟪ Λ₀ ⟫ • (PP • Ex • Ex ↑)
      ≈⟨ mid _ _ S₁₂-Λ₀ ⟩
    (Ex ↑ • Ex • PP) • Λ₀ • (PP • Ex • Ex ↑)
      ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) ((□ • □) • (□ • □ • □) • (□ • □)) Eq.refl ⟩
    C ∎
    where
    DC1 : Ex • PP • Ex ↑ • Ex • PP ≈ (Ex ↑ • Ex • PP) • Ex ↑
    DC1 = L₃-sem (Ex • PP • Ex ↑ • Ex • PP) ((Ex ↑ • Ex • PP) • Ex ↑) Eq.refl
    DC2 : PP • Ex • Ex ↑ • PP • Ex ≈ Ex ↑ • (PP • Ex • Ex ↑)
    DC2 = L₃-sem (PP • Ex • Ex ↑ • PP • Ex) (Ex ↑ • (PP • Ex • Ex ↑)) Eq.refl

  D-C : D • C ≈ C • D
  D-C = C01.carry refl SPC (CP.carry refl refl W-C)

  ZDC : Zg • D • C ≈ C • D • Zg
  ZDC = begin
    Zg • D • C          ≈⟨ trans (sym assoc) (trans (front _ Zg-D) assoc) ⟩
    D • Zg • C          ≈⟨ back _ Zg-C ⟩
    D • C • Zg          ≈⟨ trans (sym assoc) (trans (front _ D-C) assoc) ⟩
    C • D • Zg ∎

  ----------------------------------------------------------------------
  -- X = Zg D C is Y K₁ K₂

  Zo-D : Zo • D ≈ D • Zo
  Zo-D = via′ (sym WZ) (pass₂′ W-D Zg-D)

  X-form : Zg • D • C ≈ Y • K₁ • K₂
  X-form = begin
    Zg • D • C
      ≈⟨ front _ (sym WZo) ⟩
    (Λ₀ • Zo) • D • C
      ≈⟨ front _ (front _ (sym YYo)) ⟩
    ((Y • Yo) • Zo) • D • C
      ≈⟨ by-passoc (((□ • □) • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    Y • Yo • (Zo • D) • C
      ≈⟨ back _ (back _ (front _ Zo-D)) ⟩
    Y • Yo • (D • Zo) • C
      ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • (□ • □) • (□ • □)) Eq.refl ⟩
    Y • K₁ • K₂ ∎

  ----------------------------------------------------------------------
  -- Y passes B, A and F

  Y-B : Y • B ≈ B • Y
  Y-B = C12.carry S₁₂Zg refl (CN.carry refl (N₂.⟪⟫-⟪⟫ LH) (eq337 k below))

  Yo-Zg : Yo • Zg ≈ Zg • Yo
  Yo-Zg = via′ Yo≈ (pass₂′ W-Zg Y-Zg)

  Yo-A : Yo • A ≈ A • Yo
  Yo-A = CP.carry PYo PZg Yo-Zg

  Y-A : Y • A ≈ A • Y
  Y-A = via′ (trans (sym left-unit) (trans (front _ (sym Λ₀²)) (trans assoc (back _ WY))))
             (pass₂′ (eq337 k below) Yo-A)

  Y-F : Y • F ≈ F • Y
  Y-F = C12.carry S₁₂Zg (S₁₂.⟪⟫-•₃ S12X2 (sym C≈) S12X2) (CN.carry refl refl W-D)

  ----------------------------------------------------------------------
  -- The D-trick for A: A F A = UA F UA

  Wc Zc Ac Bc : Bits m → Circuit N
  Wc c = col (true ∷ true ∷ true ∷ c) Λ₀
  Zc c = col (true ∷ true ∷ true ∷ c) Zg
  Ac c = col (true ∷ true ∷ true ∷ c) A
  Bc c = col (true ∷ true ∷ true ∷ c) B

  private
    ones : Bits m
    ones = replicate m true

    col1 : ∀ (w : Circuit N) → col (true ∷ true ∷ true ∷ ones) w ≈ w
    col1 w = trans (≡→≈ (Eq.cong (λ z → z ↑ ↑ ↑ • w • z ↑ ↑ ↑) (allT m))) (trans left-unit right-unit)

  -- The H gate against the box on wire 2, in a colouring of the wires
  -- 3 … that is not all black: (339), Canon40's canonical form.
  HG-K : ∀ c → c ≢ ones → HG • col (true ∷ true ∷ true ∷ c) Λ₂ ≈ col (true ∷ true ∷ true ∷ c) Λ₂ • HG
  HG-K c c≢ = sym (CNc.carry c refl (Conj.⟪⟫-⟪⟫ (Nc c) (Nc² c) HG) (eq339c k below true c c≢))

  K-HGc : ∀ c → c ≢ ones → Λ₂ • col (true ∷ true ∷ true ∷ c) HG ≈ col (true ∷ true ∷ true ∷ c) HG • Λ₂
  K-HGc c c≢ = eq339c k below true c c≢

  πVh : πc Vh ≈ HG
  πVh = πc-•₃ πPPu πΛ₂ πPPu

  πWc : ∀ c → πc (Wc c) ≈ col (true ∷ true ∷ true ∷ c) Λ₂
  πWc c = πc-•₃ (πNc c) refl (πNc c)

  Vh-Wc : ∀ c → c ≢ ones → Vh • Wc c ≈ Wc c • Vh
  Vh-Wc c c≢ = π-back πVh (πWc c) (HG-K c c≢)

  X2-Vh : X ↑ ↑ • Vh ≈ Vh • X ↑ ↑
  X2-Vh = π-back πX2 πVh X-Hg

  N₂Wc : ∀ c → N₂.⟪ Wc c ⟫ ≈ Zc c
  N₂Wc c = conj-swap (X2-Nc c) Λ₀

  Vh-Zc : ∀ c → c ≢ ones → Vh • Zc c ≈ Zc c • Vh
  Vh-Zc c c≢ = CN.carry (N₂.⟪⟫-fix X2-Vh) (N₂Wc c) (Vh-Wc c c≢)

  S₁₂Zc : ∀ c → S₁₂.⟪ Zc c ⟫ ≈ col (true ∷ true ∷ true ∷ c) Y
  S₁₂Zc c = trans (conj-swap (loc (Ex ↑) c) Zg) (mid _ _ S₁₂Zg)

  Λ₂-Zc : ∀ c → Λ₂ • Zc c ≈ Zc c • Λ₂
  Λ₂-Zc c = S12-back (S₁₂.⟪⟫-⟪⟫ Λ₁) (S₁₂Zc c)
              (both (sym (col-ones Λ₁)) (sym (colY c)) (sym (col-pair′ (true ∷ false ∷ true ∷ c) onesN Λ₀ Λ₁ (eq336ᶜ k below))))

  f-Zc : ∀ c → f • Zc c ≈ Zc c • f
  f-Zc c = S12-back (S₁₂.⟪⟫-•₃ S12X1 (S₁₂.⟪⟫-⟪⟫ Λ₁) S12X1) (S₁₂Zc c)
             (both (sym (col-2 Λ₁)) (sym (colY c)) (sym (col-pair′ (true ∷ false ∷ true ∷ c) s110 Λ₀ Λ₁ (eq336ᶜ k below))))

  -- f is the box on wire 2 times Fo.
  f-form : f ≈ Λ₂ • Fo
  f-form = trans (sym left-unit) (trans (front _ (sym Λ₂²)) (trans assoc (back _ Fo-form)))

  Fo-Zc : ∀ c → Fo • Zc c ≈ Zc c • Fo
  Fo-Zc c = via′ (sym Fo-form) (pass₂′ (Λ₂-Zc c) (f-Zc c))

  -- C and F are the box on wire 2 between P ⊗ P on the wires 0 2.
  QC : Q.⟪ C ⟫ ≈ Λ₂
  QC = trans (Q.⟪⟫-cong (trans C≈ (S₁₂.⟪⟫-cong D≈HG)))
             (trans (Qe _) (S₁₂.⟪⟫-cong (trans (P.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ _)) (P.⟪⟫-⟪⟫ Λ₁))))

  F-Q : F ≈ Q.⟪ f ⟫
  F-Q = trans (mid _ _ (sym (conj-sym Q² QC))) (conj-swap X1Q Λ₂)

  -- Between P ⊗ P on the wires 0 1, F is Vh Fo.
  PF : P.⟪ F ⟫ ≈ Vh • Fo
  PF = begin
    P.⟪ F ⟫
      ≈⟨ P.⟪⟫-cong F-Q ⟩
    PP • (PP₀₂ • f • PP₀₂) • PP
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (PP • PP₀₂) • f • (PP₀₂ • PP)
      ≈⟨ cong klein₂ (back _ klein₁) ⟩
    Pu.⟪ f ⟫
      ≈⟨ Pu.⟪⟫-cong f-form ⟩
    Pu.⟪ Λ₂ • Fo ⟫
      ≈⟨ Pu.⟪⟫-•₂ refl PuFo ⟩
    Vh • Fo ∎

  PZc : ∀ c → P.⟪ Zc c ⟫ ≈ Ac c
  PZc c = trans (col-in PP c Zg) (mid _ _ PZg)

  F-Ac : ∀ c → c ≢ ones → F • Ac c ≈ Ac c • F
  F-Ac c c≢ = CP.carry (conj-sym eq111 PF) (PZc c) (pass₂′ (Vh-Zc c c≢) (Fo-Zc c))

  -- UA is A over every colouring of the wires 3 ….
  UA-∏ : UA ≈ ∏ (allBits m) Ac
  UA-∏ = begin
    UA
      ≈⟨ L₃-sem (X ↑ ↑ • CH ↑ • X ↑ ↑) (X ↑ ↑ • (PP • Λ□ 2 • PP) • X ↑ ↑) Eq.refl ⟩
    X ↑ ↑ • (PP ↓ • (Λ□ 2 ↓ᵏ m) • PP ↓) • X ↑ ↑
      ≈⟨ mid _ _ (mid _ _ (sym (merge-top₂ m ≤-refl))) ⟩
    X ↑ ↑ • (PP ↓ • ∏ (allBits m) Wc • PP ↓) • X ↑ ↑
      ≈⟨ mid _ _ (∏-conj (PP ↓) eq111 (allBits m) Wc) ⟩
    X ↑ ↑ • ∏ (allBits m) (λ c → P.⟪ Wc c ⟫) • X ↑ ↑
      ≈⟨ ∏-conj (X ↑ ↑) X₂² (allBits m) (λ c → P.⟪ Wc c ⟫) ⟩
    ∏ (allBits m) (λ c → N₂.⟪ P.⟪ Wc c ⟫ ⟫)
      ≈⟨ ∏-cong (allBits m) (λ c → trans (N₂.⟪⟫-cong (col-in PP c Λ₀)) (col-in (X ↑ ↑) c LH)) ⟩
    ∏ (allBits m) Ac ∎

  AFA : A • F • A ≈ UA • F • UA
  AFA = sym (begin
    UA • F • UA
      ≈⟨ back _ (back _ (trans (sym right-unit) (back _ (sym A²)))) ⟩
    UA • F • UA • (A • A)
      ≈⟨ back _ (back _ (sym assoc)) ⟩
    UA • F • (UA • A) • A
      ≈⟨ back _ (trans (sym assoc) (trans (front _ DA) assoc)) ⟩
    UA • (UA • A) • F • A
      ≈⟨ trans (sym assoc) (trans (front _ (trans (sym assoc) (trans (front _ UA²) left-unit))) refl) ⟩
    A • F • A ∎)
    where
    DA : F • (UA • A) ≈ (UA • A) • F
    DA = via (cong UA-∏ (sym (col1 A))) (pass-last m Ac F-Ac (trans (cong (col1 A) (col1 A)) A²))

  ----------------------------------------------------------------------
  -- The D-trick for B: B K₁ K₂ B = UB K₁ K₂ UB

  π2B : π2c B ≈ HG
  π2B = trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ LH)) D≈HG

  π2Bc : ∀ c → π2c (Bc c) ≈ col (true ∷ true ∷ true ∷ c) HG
  π2Bc c = π2c-•₃ (π2Nc c) π2B (π2Nc c)

  X1-HGc : ∀ c → X ↑ • col (true ∷ true ∷ true ∷ c) HG ≈ col (true ∷ true ∷ true ∷ c) HG • X ↑
  X1-HGc c = pass₃ (X1-Nc c) X-Hg (X1-Nc c)

  Λ₁-Bc : ∀ c → c ≢ ones → Λ₁ • Bc c ≈ Bc c • Λ₁
  Λ₁-Bc c c≢ = π2-back π2Λ₁ (π2Bc c) (K-HGc c c≢)

  C0-Bc : ∀ c → c ≢ ones → C0 • Bc c ≈ Bc c • C0
  C0-Bc c c≢ = π2-back (π2c-•₃ π2X0 π2Λ₁ π2X0) (π2Bc c)
                 (CX₁.carry refl (X₁.⟪⟫-fix (X1-HGc c)) (K-HGc c c≢))

  Yo-Bc : ∀ c → c ≢ ones → Yo • Bc c ≈ Bc c • Yo
  Yo-Bc c c≢ = via′ Yo-form (pass₂′ (C0-Bc c c≢) (Λ₁-Bc c c≢))

  QB : Q.⟪ B ⟫ ≈ Λ₀
  QB = trans (Qe B) (trans (S₁₂.⟪⟫-cong (trans (P.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ _)) (P.⟪⟫-⟪⟫ Λ₀))) S₁₂-Λ₀)

  QBc : ∀ c → Q.⟪ Bc c ⟫ ≈ Wc c
  QBc c = trans (conj-swap (loc (Ex ↑ • PP • Ex ↑) c) B) (mid _ _ QB)

  QD : Q.⟪ D ⟫ ≈ Hd
  QD = begin
    Q.⟪ D ⟫
      ≈⟨ Q.⟪⟫-cong D≈HG ⟩
    PP₀₂ • (PP • Λ₁ • PP) • PP₀₂
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (PP₀₂ • PP) • Λ₁ • (PP • PP₀₂)
      ≈⟨ cong klein₁ (back _ klein₂) ⟩
    Hd ∎

  QZo : Q.⟪ Zo ⟫ ≈ Zo
  QZo = trans (Qe Zo) (S₁₂.⟪⟫-cong (trans (P.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ Yo)) PYo))

  τHd : T.⟪ Hd ⟫ ≈ HG
  τHd = T.⟪⟫-•₃ τPPu τΛ₁ τPPu

  τWc : ∀ c → T.⟪ Wc c ⟫ ≈ col (true ∷ true ∷ true ∷ c) Λ₂
  τWc c = T.⟪⟫-•₃ (τNc c) τΛ₀ (τNc c)

  Hd-Wc : ∀ c → c ≢ ones → Hd • Wc c ≈ Wc c • Hd
  Hd-Wc c c≢ = τ-back τHd (τWc c) (HG-K c c≢)

  Zo-Wc : ∀ c → Zo • Wc c ≈ Wc c • Zo
  Zo-Wc c = via′ (sym WZ) (pass₂′ (eq335 k below (true ∷ true ∷ true ∷ c))
                  (both (sym (col-2 Λ₀)) refl (col-pair s110 (true ∷ true ∷ true ∷ c) Λ₀ (eq335 k below))))

  S₁₂Wc : ∀ c → S₁₂.⟪ Wc c ⟫ ≈ Wc c
  S₁₂Wc c = trans (conj-swap (loc (Ex ↑) c) Λ₀) (mid _ _ S₁₂-Λ₀)

  Λ₂-Wc : ∀ c → Λ₂ • Wc c ≈ Wc c • Λ₂
  Λ₂-Wc c = S12-back (S₁₂.⟪⟫-⟪⟫ Λ₁) (S₁₂Wc c)
              (both (sym (col-ones Λ₁)) refl (sym (col-pair′ (true ∷ true ∷ true ∷ c) onesN Λ₀ Λ₁ (eq336ᶜ k below))))

  D-Bc : ∀ c → c ≢ ones → D • Bc c ≈ Bc c • D
  D-Bc c c≢ = Q-back QD (QBc c) (Hd-Wc c c≢)

  Zo-Bc : ∀ c → Zo • Bc c ≈ Bc c • Zo
  Zo-Bc c = Q-back QZo (QBc c) (Zo-Wc c)

  C-Bc : ∀ c → C • Bc c ≈ Bc c • C
  C-Bc c = Q-back QC (QBc c) (Λ₂-Wc c)

  K-Bc : ∀ c → c ≢ ones → (K₁ • K₂) • Bc c ≈ Bc c • (K₁ • K₂)
  K-Bc c c≢ = pass₂′ (pass₂′ (Yo-Bc c c≢) (D-Bc c c≢)) (pass₂′ (Zo-Bc c) (C-Bc c))

  UB-∏ : UB ≈ ∏ (allBits m) Bc
  UB-∏ = begin
    UB
      ≈⟨ L₃-sem (Ex ↑ • CH ↑ • Ex ↑) (Ex ↑ • (PP • Λ□ 2 • PP) • Ex ↑) Eq.refl ⟩
    Ex ↑ • (PP ↓ • (Λ□ 2 ↓ᵏ m) • PP ↓) • Ex ↑
      ≈⟨ mid _ _ (mid _ _ (sym (merge-top₂ m ≤-refl))) ⟩
    Ex ↑ • (PP ↓ • ∏ (allBits m) Wc • PP ↓) • Ex ↑
      ≈⟨ mid _ _ (∏-conj (PP ↓) eq111 (allBits m) Wc) ⟩
    Ex ↑ • ∏ (allBits m) (λ c → P.⟪ Wc c ⟫) • Ex ↑
      ≈⟨ ∏-conj (Ex ↑) Ex↑² (allBits m) (λ c → P.⟪ Wc c ⟫) ⟩
    ∏ (allBits m) (λ c → S₁₂.⟪ P.⟪ Wc c ⟫ ⟫)
      ≈⟨ ∏-cong (allBits m) (λ c → trans (S₁₂.⟪⟫-cong (col-in PP c Λ₀)) (col-in (Ex ↑) c LH)) ⟩
    ∏ (allBits m) Bc ∎

  BKB : B • (K₁ • K₂) • B ≈ UB • (K₁ • K₂) • UB
  BKB = sym (begin
    UB • K • UB
      ≈⟨ back _ (back _ (trans (sym right-unit) (back _ (sym B²)))) ⟩
    UB • K • UB • (B • B)
      ≈⟨ back _ (back _ (sym assoc)) ⟩
    UB • K • (UB • B) • B
      ≈⟨ back _ (trans (sym assoc) (trans (front _ DB) assoc)) ⟩
    UB • (UB • B) • K • B
      ≈⟨ trans (sym assoc) (trans (front _ (trans (sym assoc) (trans (front _ UB²) left-unit))) refl) ⟩
    B • K • B ∎)
    where
    K : Circuit N
    K = K₁ • K₂
    DB : K • (UB • B) ≈ (UB • B) • K
    DB = via (cong UB-∏ (sym (col1 B))) (pass-last m Bc K-Bc (trans (cong (col1 B) (col1 B)) B²))

  ----------------------------------------------------------------------
  -- Core46 from the commutation of UA F UA and UB K₁ K₂ UB

  Endgame : Set
  Endgame = (UA • F • UA) • (UB • (K₁ • K₂) • UB) ≈ (UB • (K₁ • K₂) • UB) • (UA • F • UA)

  reduce : Endgame → Core46 {m}
  reduce eg = begin
    A • B • Zg • D • C • B • A • F
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • (□ • (□ • □ • □) • □) • (□ • □)) Eq.refl ⟩
    A • Q′ • (A • F)
      ≈⟨ back _ (back _ (trans (sym right-unit) (back _ (sym A²)))) ⟩
    A • Q′ • ((A • F) • (A • A))
      ≈⟨ back _ (back _ (by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl)) ⟩
    A • Q′ • (P′ • A)
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym PQ)) assoc)) ⟩
    A • P′ • (Q′ • A)
      ≈⟨ by-passoc (□ • (□ • □ • □) • □ • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (A • A) • F • A • Q′ • A
      ≈⟨ trans (front _ A²) left-unit ⟩
    F • A • Q′ • A
      ≈⟨ back _ (back _ (front _ (back _ (front _ ZDC)))) ⟩
    F • A • (B • (C • D • Zg) • B) • A
      ≈⟨ by-passoc (□ • □ • (□ • (□ • □ • □) • □) • □) (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    F • A • B • C • D • Zg • B • A ∎
    where
    P′ Q′ R : Circuit N
    P′ = A • F • A
    Q′ = B • (Zg • D • C) • B
    R  = UB • (K₁ • K₂) • UB
    -- Y passes A F A, hence UA F UA.
    YP : Y • P′ ≈ P′ • Y
    YP = pass₃ Y-A Y-F Y-A
    Q-form : Q′ ≈ Y • R
    Q-form = begin
      B • (Zg • D • C) • B       ≈⟨ back _ (front _ X-form) ⟩
      B • (Y • K₁ • K₂) • B      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • (□ • □) • □) Eq.refl ⟩
      (B • Y) • (K₁ • K₂) • B    ≈⟨ front _ (sym Y-B) ⟩
      (Y • B) • (K₁ • K₂) • B    ≈⟨ assoc ⟩
      Y • B • (K₁ • K₂) • B      ≈⟨ back _ BKB ⟩
      Y • R ∎
    PQ : P′ • Q′ ≈ Q′ • P′
    PQ = both AFA Q-form (pass₂ (sym (via (sym AFA) YP)) eg)
