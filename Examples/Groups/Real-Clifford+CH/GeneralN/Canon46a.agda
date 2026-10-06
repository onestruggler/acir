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
-- module parameter of `reduce` (GeneralN.Canon46b).  The argument is
-- Canon46aGen's, generic in the width; this is its instance from five
-- wires on, the box facts from canonN, (335), (336) (BoxComm), (276)
-- (ZXPass), (337) (Box337) and MergeAll, the H gate Col.Hg with (338)
-- (Box338, Box338Eq) and (339) (Canon40).  Every identity was checked
-- numerically at five wires first (scratchpad t46agda.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon46a
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true)
open import Data.Nat using (ℕ ; s≤s)
open import Data.Nat.Properties using (n<1+n ; ≤-refl)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (box276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (sep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box337 complete₂ complete₃ using (eq337 ; col-2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (eq339c)
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46aGen complete₂ complete₃ as G46a

------------------------------------------------------------------------
-- At width 5 + k

module At (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m : ℕ
    N = ₁₊ (₄₊ k)
    m = ₂₊ k

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    Λ₀′ : Circuit N
    Λ₀′ = Λ□ (₄₊ k)

  open Tools (N VRel,_===_)
  open XY k below public using (eq338xy ; X-Hg ; S-ΛH)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₂)

  --------------------------------------------------------------------
  -- The width-specific inputs of Canon46aGen

  canon : Canon (₂₊ k)
  canon = canonN k completes

  HG : Circuit N
  HG = Hg (₂₊ k)

  s12Λ₀ : Ex ↑ • Λ₀′ • Ex ↑ ≈ Λ₀′
  s12Λ₀ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ (lemma-cong↑ _ _ Ex²)) right-unit)))

  mt : ∏ (allBits m) (λ c → col (true ∷ true ∷ true ∷ c) Λ₀′) ≈ Λ□ 2 ↓ᵏ m
  mt = merge-top₂ m ≤-refl

  sepΛ : Λ₀′ • (X ↑ ↑ • HG • X ↑ ↑) ≈ (X ↑ ↑ • HG • X ↑ ↑) • Λ₀′
  sepΛ = trans (back _ (sym (col-2 HG))) (trans (sep k below (replicate (₂₊ k) true)) (front _ (col-2 HG)))

  eq339c′ : ∀ (c : Bits m) → c ≢ replicate m true →
            (Ex ↑ • (Ex ↓ • Λ₀′ • Ex ↓) • Ex ↑) • col (true ∷ true ∷ true ∷ c) HG
            ≈ col (true ∷ true ∷ true ∷ c) HG • (Ex ↑ • (Ex ↓ • Λ₀′ • Ex ↓) • Ex ↑)
  eq339c′ c c≢ = eq339c k below true c c≢

  PYo′ : PP ↓ • Λ□ (₃₊ k) ↑ • PP ↓ ≈ Λ□ (₃₊ k) ↑
  PYo′ = box276 (₁₊ k) c

  open G46a {₁₊ k} canon HG refl S-ΛH X-Hg eq338xy s12Λ₀ mt (eq335 k below) (eq336ᶜ k below) sepΛ
            (eq337 k below) eq339c′ PYo′ public
