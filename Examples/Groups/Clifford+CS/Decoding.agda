------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of words over P′ into n-qubit circuits (the analogue of
-- Clément's Definition 8.3)
--
-- A letter on two consecutive indices is a gadget of MultiControlled
-- placed by the layout of the pair's Gray codes — the target where
-- they differ, a control of the common bit elsewhere — and oriented by
-- the bit of the first index at the target: the phase pair i_a i_{a+1}⁻¹
-- has its i at the code of a, the rotation (−1)_a X_{a,a+1} is XZ when
-- that bit is 0, and the hybrid K_[a,a+1] i_a⁻¹ has a at bit 1.  The
-- other letters follow the rules of P′ (Auxiliary.Rules), in written
-- order: a phase pair is a chain of consecutive ones (pp-tele), a
-- signed exchange shrinks from the bottom (px-shrink₁, px-shrink₂),
-- its sign moves to the pair by two phase pairs (px-sign), the double
-- exchange splits (dx-split), the hybrid's sink moves along a phase
-- pair (ki-sink), and the hybrid's pair closes by consecutive
-- rotations: (−1)_{a+1} X_{a,a+1} carries K_[a+1,b] i_{a+1}⁻¹ to
-- K_[a,b] i_a⁻¹, the sink travelling with the pair.  So those rules
-- decode by definition, and no fresh index is needed anywhere.
--
-- Words over P′ and circuits are both read in written order (a word
-- w • v denotes ⟦ w ⟧ · ⟦ v ⟧), so `d` extends to words letter by
-- letter, with no reversal — unlike Real-Clifford+CH.Decoding, whose
-- paper composes with ∘.  Checked against the letters' matrices at
-- n = 4 and 5 in scratchpad/dec.py, and in Agda by DecodingChecks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Decoding (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Fin using (toℕ)
open import Data.Nat using (zero ; suc ; _∸_ ; _<ᵇ_ ; _≡ᵇ_)
open import Data.Vec using (zipWith)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics.Algebra using (Bits)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled
open import Examples.Groups.Clifford+CS.Numbering (₄₊ m) using (N)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (gray ; toBits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)

private
  n : ℕ
  n = ₄₊ m

------------------------------------------------------------------------
-- The layout of a consecutive pair

-- The Gray code of an index.
gcode : ℕ → Bits n
gcode k = gray (toBits n k)

-- The slot of a wire for two codes: the target where they differ, a
-- control of the common bit elsewhere.
slot : Bool → Bool → Slot
slot b b′ = if b xor b′ then tgt else ctrl b

layout□ : ℕ → Layout n
layout□ a = zipWith slot (gcode a) (gcode (suc a))

-- The bit of the code of a on the target wire.
βof : ℕ → Bool
βof a = lookupℕ (tgtWire (layout□ a)) (gcode a)

------------------------------------------------------------------------
-- The letters on consecutive indices

-- i_a i_{a+1}⁻¹, and i_{a+1} i_a⁻¹.
dPP₁ dPP₁′ : ℕ → Circuit n
dPP₁  a = mc (βof a)       (layout□ a) (G-pp (₁₊ m))
dPP₁′ a = mc (not (βof a)) (layout□ a) (G-pp (₁₊ m))

-- (−1)_a X_{a,a+1} and (−1)_{a+1} X_{a,a+1}.
lo₁ hi₁ : ℕ → Circuit n
lo₁ a = mc (βof a)       (layout□ a) (G-rot (₁₊ m))
hi₁ a = mc (not (βof a)) (layout□ a) (G-rot (₁₊ m))

-- K_[a,a+1] i_a⁻¹.
dKI₁ : ℕ → Circuit n
dKI₁ a = mc (not (βof a)) (layout□ a) (G-ki (₁₊ m))

------------------------------------------------------------------------
-- i_a i_b⁻¹

-- The chain from a up d steps, and the inverse chain.
dPP-up dPP-dn : ℕ → ℕ → Circuit n
dPP-up a zero    = ε
dPP-up a (suc d) = dPP₁ a • dPP-up (suc a) d
dPP-dn a zero    = ε
dPP-dn a (suc d) = dPP₁′ a • dPP-dn (suc a) d

dPP : ℕ → ℕ → Circuit n
dPP a b = if a <ᵇ b then dPP-up a (b ∸ a) else dPP-dn b (a ∸ b)

------------------------------------------------------------------------
-- (−1)_c X_[a,b]

-- (−1)_a X_{a,a+d} and (−1)_{a+d} X_{a,a+d}, shrinking from the bottom.
dLo dHi : ℕ → ℕ → Circuit n
dLo a zero       = ε
dLo a (suc zero) = lo₁ a
dLo a (₂₊ d)     = hi₁ a • dLo (suc a) (suc d) • lo₁ a
dHi a zero       = ε
dHi a (suc zero) = hi₁ a
dHi a (₂₊ d)     = hi₁ a • dHi (suc a) (suc d) • lo₁ a

-- (−1)_c X_[a,b] for a < b, its tests passed as arguments so that proofs
-- can rewrite them: whether c is a, b, or neither.
dPXs : Bool → Bool → ℕ → ℕ → ℕ → Circuit n
dPXs true  _     c a b = dLo a (b ∸ a)
dPXs false true  c a b = dHi a (b ∸ a)
dPXs false false c a b = dPP c a • dPP c a • dLo a (b ∸ a)

dPX : ℕ → ℕ → ℕ → Circuit n
dPX c a b = dPXs (c ≡ᵇ a) (c ≡ᵇ b) c a b

------------------------------------------------------------------------
-- X_[a,b] X_[c,d]

dDX : ℕ → ℕ → ℕ → ℕ → Circuit n
dDX a b c d = dPX a a b • dPX b c d

------------------------------------------------------------------------
-- K_[a,b] i_s⁻¹

-- K_[a,a+d] i_a⁻¹: the pair closed by consecutive rotations.
dKIa : ℕ → ℕ → Circuit n
dKIa a zero       = ε
dKIa a (suc zero) = dKI₁ a
dKIa a (₂₊ d)     = hi₁ a • dKIa (suc a) (suc d) • lo₁ a

dKI : ℕ → ℕ → ℕ → Circuit n
dKI a b s = dKIa a (b ∸ a) • dPP a s

------------------------------------------------------------------------
-- The decoding

d : GenP N → Circuit n
d (pp a b)         = dPP (toℕ a) (toℕ b)
d (px c a b _)     = dPX (toℕ c) (toℕ a) (toℕ b)
d (dx a b c e _ _) = dDX (toℕ a) (toℕ b) (toℕ c) (toℕ e)
d (ki a b s _)     = dKI (toℕ a) (toℕ b) (toℕ s)
