------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded letters of rule (46) of Figure 8 (Clément, Definition
-- 8.3), and the statement they are to satisfy
--
-- (46) has five Hadamard pairs and one sign pair, all on indices among
-- 0 … 7, whose Gray codes agree on the wires 3 … (Lemma88.Layout).  So
-- every decoded letter is a gate on the wires 0 1 2 between the
-- negations of the wires 3 … where t is white, and what is left of it
-- there is one of the six gates below, named by the letter it decodes:
-- the H gate (ΛH, H on wire 1, box wire 0) with its H and box wires
-- carried by swaps and its wire-2 control negated where the code is
-- white, and the box negated on wire 2 for the sign pair on 2 3.
-- `Core46` is the rule between the negations, with the decodings in
-- written order reversed (Lemma88.Rule46 reduces (46) to it).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 {m : ℕ} where

open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)

-- H_[0,3] H_[1,2]: box wire 0, H on wire 1, white on wire 2.
h0312 : Circuit (₃₊ m)
h0312 = X ↑ ↑ • ΛH (₁₊ m) • X ↑ ↑

-- H_[3,4] H_[2,5]: box wire 0, H on wire 2, black on wire 1.
h3425 : Circuit (₃₊ m)
h3425 = Ex ↑ • ΛH (₁₊ m) • Ex ↑

-- (−1)_[2] (−1)_[3]: the box on wire 0, black on 1, white on 2.
z23 : Circuit (₃₊ m)
z23 = X ↑ ↑ • Λ□ (₂₊ m) • X ↑ ↑

-- H_[7,6] H_[4,5]: H on wire 0, box wire 1, black on wire 2.
h7645 : Circuit (₃₊ m)
h7645 = Ex ↓ • ΛH (₁₊ m) • Ex ↓

-- H_[3,2] H_[4,5]: H on wire 0, box wire 2, black on wire 1.
h3245 : Circuit (₃₊ m)
h3245 = (Ex ↑ • Ex ↓) • ΛH (₁₊ m) • (Ex ↓ • Ex ↑)

-- H_[0,1] H_[7,6]: the same, white on wire 1.
h0176 : Circuit (₃₊ m)
h0176 = X ↑ • h3245 • X ↑

-- (46) between the negations, in the order the decodings compose.
Core46 : Set
Core46 = (₃₊ m) ⊢ h0312 • h3425 • z23 • h7645 • h3245 • h3425 • h0312 • h0176
                 ≈ h0176 • h0312 • h3425 • h3245 • h7645 • z23 • h3425 • h0312
