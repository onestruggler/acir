/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): Figure 6's (d3)

(d3) at `0, 1, 2, 3`, `(H_[2,3] H_[0,2] H_[1,3])⁴ ≈ H_[0,1] H_[2,3]`, follows
from Clément's (20) at `0, 1, 2, 3` (Figure 7's (d3*)) along the derivation
of Lemma A.1 (Proof of Equation (d3)), each of its steps but the one by
(d3*) being a commutation of two generators on disjoint pairs or an identity
on at most three indices (`chA`).  The same at `0, 2, 1, 3` (`chB`, the
other order of the middle indices).  The congruence of Claim B pulled back
along any increasing `g : Fin 4 → Fin 2ⁿ` contains the identities on three
indices (Figure 6 is complete on three indices, where it has no (d3)), the
commutations and (20) (`gb20`); so it contains (d3) (`gb_d3`).

The chains are generated (`.handover-scratch/thm410/ib/gend3.py`): the lines
of the printed derivation, split into steps by a search, each step checked
numerically.
-/
import QCert.RealCliffordCH.Sec8.A.ItemBPull
import QCert.RealCliffordCH.Sec8.A.ItemB20

namespace QCert.RealCliffordCH.Sec8

open QCert.HadamardPi FreeMonoid Chk

/-- (d3), shape A: the two sides. -/
def d3LA : List (HadamardPi.Gen 4) := [hL 2 3, hL 0 2, hL 1 3, hL 2 3, hL 0 2, hL 1 3, hL 2 3, hL 0 2, hL 1 3, hL 2 3, hL 0 2, hL 1 3]
/-- The right-hand side. -/
def d3RA : List (HadamardPi.Gen 4) := [hL 0 1, hL 2 3]
/-- Clément's (20) at the indices the chain uses. -/
def e20A : List (List (HadamardPi.Gen 4) × List (HadamardPi.Gen 4)) :=
  [([hL 0 1, hL 0 2, hL 1 3, hL 0 1, zL 0, zL 1, hL 0 2, hL 1 3],
    [hL 0 2, hL 1 3, hL 0 1, zL 0, zL 1, hL 0 2, hL 1 3, hL 0 1])]
/-- The chain. -/
def chA : List (CS 4 3) := [
  .sem ![0, 1, 3] [] [zL 2, zL 2] 1,
  .sem ![0, 2, 3] [zL 2] [zL 1, zL 2, zL 1] 1,
  .sem ![0, 2, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 3,
  .sem ![0, 1, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 5,
  .rel .b5 [0, 2, 1, 3] 4 true,
  .sem ![0, 1, 2] [xL 0 2] [zL 0, xL 0 2, zL 2] 5,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 1 2] [hL 0 1, zL 0, xL 0 2] 7,
  .sem ![0, 1, 2] [xL 0 2, hL 1 2, zL 1] [zL 0, hL 0 1, xL 0 2] 6,
  .sem ![0, 1, 2] [zL 0, zL 0] [] 5,
  .rel .b5 [1, 3, 0, 2] 7 true,
  .sem ![0, 1, 2] [xL 0 2, hL 0 2] [hL 0 2, zL 2] 6,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 0 2] [hL 0 2, zL 1, zL 2] 7,
  .sem ![0, 2, 3] [zL 1, zL 2, hL 1 2] [hL 1 2, zL 1, zL 2] 8,
  .sem ![0, 2, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 9,
  .sem ![0, 1, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 11,
  .rel .b5 [0, 2, 1, 3] 10 true,
  .sem ![0, 1, 2] [xL 0 2] [zL 0, xL 0 2, zL 2] 11,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 1 2] [hL 0 1, zL 0, xL 0 2] 13,
  .sem ![0, 1, 2] [xL 0 2, hL 1 2, zL 1] [zL 0, hL 0 1, xL 0 2] 12,
  .sem ![0, 1, 2] [zL 0, zL 0] [] 11,
  .rel .b5 [1, 3, 0, 2] 13 true,
  .sem ![0, 1, 2] [xL 0 2, hL 0 2] [hL 0 2, zL 2] 12,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 0 2] [hL 0 2, zL 1, zL 2] 13,
  .sem ![0, 1, 2] [] [zL 0, zL 0] 6,
  .sem ![0, 1, 2] [zL 0] [zL 1, zL 0, zL 1] 7,
  .sem ![0, 1, 3] [zL 1] [zL 1, zL 2, zL 2] 7,
  .sem ![0, 2, 3] [zL 2] [zL 1, zL 2, zL 1] 8,
  .sem ![0, 2, 3] [zL 1, zL 2, zL 0] [zL 2, zL 0, zL 1] 10,
  .sem ![0, 1, 2] [zL 2, zL 1, hL 0 2] [zL 2, hL 0 2, zL 1] 12,
  .sem ![0, 1, 2] [zL 0, zL 2, hL 0 2] [xL 0 2, hL 0 2, zL 0] 11,
  .sem ![0, 2, 3] [zL 2, xL 0 1, hL 0 1] [hL 0 1, zL 1, zL 2] 10,
  .sem ![0, 2, 3] [zL 1, zL 2, zL 0] [zL 1, zL 0, zL 2] 11,
  .sem ![0, 1, 3] [zL 2, zL 1, hL 1 2] [xL 1 2, hL 1 2, zL 1] 13,
  .sem ![0, 1, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 2, zL 0] 12,
  .sem ![1, 2, 3] [zL 1, hL 0 2] [hL 0 2, zL 1] 11,
  .sem ![0, 2, 3] [zL 0] [hL 1 2, zL 0, hL 1 2] 14,
  .sem ![0, 2, 3] [zL 1, zL 2, hL 1 2] [hL 1 2, zL 1, zL 2] 12,
  .sem ![1, 2, 3] [hL 1 2, zL 0, hL 1 2] [zL 0] 16,
  .sem ![0, 2, 3] [zL 1, zL 2, zL 0] [zL 2, zL 0, zL 1] 13,
  .sem ![0, 1, 2] [zL 2, zL 1, hL 0 2] [zL 2, hL 0 2, zL 1] 15,
  .sem ![0, 1, 2] [zL 0, zL 2, hL 0 2] [xL 0 2, hL 0 2, zL 0] 14,
  .sem ![0, 2, 3] [zL 2, xL 0 1, hL 0 1] [hL 0 1, zL 1, zL 2] 13,
  .sem ![0, 2, 3] [zL 1, zL 2, zL 0] [zL 1, zL 0, zL 2] 14,
  .sem ![0, 1, 3] [zL 2, zL 1, hL 1 2] [xL 1 2, hL 1 2, zL 1] 16,
  .sem ![0, 1, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 2, zL 0] 15,
  .sem ![1, 2, 3] [zL 1, hL 0 2] [hL 0 2, zL 1] 14,
  .sem ![0, 2, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 8,
  .sem ![0, 1, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 10,
  .rel .b5 [0, 2, 1, 3] 9 true,
  .sem ![0, 1, 2] [xL 0 2] [zL 0, xL 0 2, zL 2] 10,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 1 2] [hL 0 1, zL 0, xL 0 2] 12,
  .sem ![0, 1, 2] [xL 0 2, hL 1 2, zL 1] [zL 0, hL 0 1, xL 0 2] 11,
  .sem ![0, 1, 2] [zL 0, zL 0] [] 10,
  .rel .b5 [1, 3, 0, 2] 12 true,
  .sem ![0, 1, 2] [xL 0 2, hL 0 2] [hL 0 2, zL 2] 11,
  .sem ![1, 2, 3] [zL 1, xL 0 2, hL 0 2] [hL 0 2, zL 1, zL 2] 12,
  .sem ![0, 2, 3] [zL 2, zL 1, zL 2] [zL 1] 14,
  .sem ![0, 1, 2] [zL 2, zL 2] [] 13,
  .ext 0 3 false,
  .rel .b6 [1, 3, 0, 2] 10 true,
  .sem ![0, 1, 2] [hL 0 2, hL 0 2] [] 9,
  .sem ![0, 1, 3] [hL 1 2, hL 1 2] [] 9,
  .sem ![0, 1, 2] [zL 0, zL 1, zL 0] [zL 1] 7,
  .sem ![0, 1, 2] [zL 1, zL 1] [] 7,
  .sem ![0, 1, 2] [hL 0 1, hL 0 1] [] 6,
  .rel .b6 [1, 3, 0, 2] 5 true,
  .sem ![0, 1, 2] [hL 0 2, hL 0 2] [] 4,
  .sem ![0, 1, 3] [hL 1 2, hL 1 2] [] 4,
  .sem ![0, 1, 3] [zL 2, hL 0 1] [hL 0 1, zL 2] 2,
  .sem ![0, 2, 3] [zL 2, zL 1, zL 2] [zL 1] 3,
  .sem ![0, 1, 2] [zL 2, hL 0 1, zL 2] [hL 0 1] 1,
  .rel .b6 [2, 3, 0, 1] 0 true]
theorem runA : Chk.run e20A chA d3LA = some d3RA := by decide +kernel

/-- (d3), shape B: the two sides. -/
def d3LB : List (HadamardPi.Gen 4) := [hL 1 3, hL 0 1, hL 2 3, hL 1 3, hL 0 1, hL 2 3, hL 1 3, hL 0 1, hL 2 3, hL 1 3, hL 0 1, hL 2 3]
/-- The right-hand side. -/
def d3RB : List (HadamardPi.Gen 4) := [hL 0 2, hL 1 3]
/-- Clément's (20) at the indices the chain uses. -/
def e20B : List (List (HadamardPi.Gen 4) × List (HadamardPi.Gen 4)) :=
  [([hL 0 2, hL 0 1, hL 2 3, hL 0 2, zL 0, zL 2, hL 0 1, hL 2 3],
    [hL 0 1, hL 2 3, hL 0 2, zL 0, zL 2, hL 0 1, hL 2 3, hL 0 2])]
/-- The chain. -/
def chB : List (CS 4 3) := [
  .sem ![0, 1, 3] [] [zL 2, zL 2] 1,
  .sem ![0, 1, 3] [zL 2] [zL 1, zL 2, zL 1] 1,
  .sem ![0, 1, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 3,
  .sem ![0, 2, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 5,
  .rel .b5 [0, 1, 2, 3] 4 true,
  .sem ![1, 2, 3] [xL 1 2, hL 0 2] [hL 0 1, xL 1 2] 6,
  .sem ![0, 1, 2] [xL 0 1, hL 1 2] [hL 0 2, xL 0 1] 5,
  .rel .b5 [2, 3, 0, 1] 7 true,
  .sem ![0, 1, 2] [xL 0 1, hL 0 1] [hL 0 1, zL 1] 6,
  .sem ![1, 2, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 0, zL 2] 7,
  .sem ![0, 1, 3] [zL 1, zL 2, hL 1 2] [hL 1 2, zL 1, zL 2] 8,
  .sem ![0, 1, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 9,
  .sem ![0, 2, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 11,
  .rel .b5 [0, 1, 2, 3] 10 true,
  .sem ![1, 2, 3] [xL 1 2, hL 0 2] [hL 0 1, xL 1 2] 12,
  .sem ![0, 1, 2] [xL 0 1, hL 1 2] [hL 0 2, xL 0 1] 11,
  .rel .b5 [2, 3, 0, 1] 13 true,
  .sem ![0, 1, 2] [xL 0 1, hL 0 1] [hL 0 1, zL 1] 12,
  .sem ![1, 2, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 0, zL 2] 13,
  .sem ![0, 1, 2] [] [zL 0, zL 0] 6,
  .sem ![0, 1, 2] [zL 0] [zL 2, zL 0, zL 2] 7,
  .sem ![0, 2, 3] [zL 1] [zL 1, zL 2, zL 2] 7,
  .sem ![0, 1, 3] [zL 2] [zL 1, zL 2, zL 1] 8,
  .sem ![0, 1, 3] [zL 1, zL 2, zL 0] [zL 2, zL 0, zL 1] 10,
  .sem ![0, 1, 2] [zL 1, zL 2, hL 0 1] [zL 1, hL 0 1, zL 2] 12,
  .sem ![0, 1, 2] [zL 0, zL 1, hL 0 1] [xL 0 1, hL 0 1, zL 0] 11,
  .sem ![0, 1, 3] [zL 2, xL 0 1, hL 0 1] [hL 0 1, zL 1, zL 2] 10,
  .sem ![0, 1, 3] [zL 1, zL 2, zL 0] [zL 1, zL 0, zL 2] 11,
  .sem ![0, 2, 3] [zL 2, zL 1, hL 1 2] [xL 1 2, hL 1 2, zL 1] 13,
  .sem ![0, 2, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 2, zL 0] 12,
  .sem ![1, 2, 3] [zL 0, hL 1 2] [hL 1 2, zL 0] 11,
  .sem ![0, 1, 3] [zL 0] [hL 1 2, zL 0, hL 1 2] 14,
  .sem ![0, 1, 3] [zL 1, zL 2, hL 1 2] [hL 1 2, zL 1, zL 2] 12,
  .sem ![1, 2, 3] [hL 0 2, zL 1, hL 0 2] [zL 1] 16,
  .sem ![0, 1, 3] [zL 1, zL 2, zL 0] [zL 2, zL 0, zL 1] 13,
  .sem ![0, 1, 2] [zL 1, zL 2, hL 0 1] [zL 1, hL 0 1, zL 2] 15,
  .sem ![0, 1, 2] [zL 0, zL 1, hL 0 1] [xL 0 1, hL 0 1, zL 0] 14,
  .sem ![0, 1, 3] [zL 2, xL 0 1, hL 0 1] [hL 0 1, zL 1, zL 2] 13,
  .sem ![0, 1, 3] [zL 1, zL 2, zL 0] [zL 1, zL 0, zL 2] 14,
  .sem ![0, 2, 3] [zL 2, zL 1, hL 1 2] [xL 1 2, hL 1 2, zL 1] 16,
  .sem ![0, 2, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 2, zL 0] 15,
  .sem ![1, 2, 3] [zL 0, hL 1 2] [hL 1 2, zL 0] 14,
  .sem ![0, 1, 3] [zL 1, zL 2, hL 0 1] [hL 0 1, xL 0 1, zL 2] 8,
  .sem ![0, 2, 3] [zL 2, hL 1 2] [hL 1 2, xL 1 2] 10,
  .rel .b5 [0, 1, 2, 3] 9 true,
  .sem ![1, 2, 3] [xL 1 2, hL 0 2] [hL 0 1, xL 1 2] 11,
  .sem ![0, 1, 2] [xL 0 1, hL 1 2] [hL 0 2, xL 0 1] 10,
  .rel .b5 [2, 3, 0, 1] 12 true,
  .sem ![0, 1, 2] [xL 0 1, hL 0 1] [hL 0 1, zL 1] 11,
  .sem ![1, 2, 3] [zL 0, xL 1 2, hL 1 2] [hL 1 2, zL 0, zL 2] 12,
  .sem ![0, 1, 3] [zL 2, zL 1, zL 2] [zL 1] 14,
  .sem ![0, 1, 2] [zL 1, zL 1] [] 13,
  .ext 0 3 false,
  .rel .b6 [2, 3, 0, 1] 10 true,
  .sem ![0, 1, 2] [hL 0 1, hL 0 1] [] 9,
  .sem ![0, 2, 3] [hL 1 2, hL 1 2] [] 9,
  .sem ![0, 1, 2] [zL 0, zL 2, zL 0] [zL 2] 7,
  .sem ![0, 1, 2] [zL 2, zL 2] [] 7,
  .sem ![0, 1, 2] [hL 0 2, hL 0 2] [] 6,
  .rel .b6 [2, 3, 0, 1] 5 true,
  .sem ![0, 1, 2] [hL 0 1, hL 0 1] [] 4,
  .sem ![0, 2, 3] [hL 1 2, hL 1 2] [] 4,
  .sem ![0, 2, 3] [zL 2, hL 0 1] [hL 0 1, zL 2] 2,
  .sem ![0, 1, 3] [zL 2, zL 1, zL 2] [zL 1] 3,
  .sem ![0, 1, 2] [zL 1, hL 0 2, zL 1] [hL 0 2] 1,
  .rel .b6 [1, 3, 0, 2] 0 true]
theorem runB : Chk.run e20B chB d3LB = some d3RB := by decide +kernel

variable {n : ℕ}

theorem e20_gb (hn : 3 ≤ n) (g : Fin 4 → Fin (2 ^ n)) (hg : StrictMono g) {i0 i1 i2 i3 : Fin 4}
    (h01 : i0 < i1) (h02 : i0 < i2) (h13 : i1 < i3) (h12 : i1 ≠ i2) (h23 : i2 ≠ i3) :
    GB n (wmap g hg (ofList [HadamardPi.Gen.H i0 i1 h01, HadamardPi.Gen.H i0 i2 h02, HadamardPi.Gen.H i1 i3 h13, HadamardPi.Gen.H i0 i1 h01,
        HadamardPi.Gen.Z i0, HadamardPi.Gen.Z i1, HadamardPi.Gen.H i0 i2 h02, HadamardPi.Gen.H i1 i3 h13]))
      (wmap g hg (ofList [HadamardPi.Gen.H i0 i2 h02, HadamardPi.Gen.H i1 i3 h13, HadamardPi.Gen.H i0 i1 h01, HadamardPi.Gen.Z i0, HadamardPi.Gen.Z i1,
        HadamardPi.Gen.H i0 i2 h02, HadamardPi.Gen.H i1 i3 h13, HadamardPi.Gen.H i0 i1 h01])) := by
  rw [wmap_ofList, wmap_ofList]
  exact gb20 hn (hg h01) (hg h02) (hg h13) (fun e => h12 (hg.injective e))
    (fun e => h23 (hg.injective e))

/-- (d3) at `0, 1, 2, 3` moved along any increasing `g`. -/
theorem gb_d3A (hn : 3 ≤ n) (g : Fin 4 → Fin (2 ^ n)) (hg : StrictMono g) :
    GB n (wmap g hg (ofList d3LA)) (wmap g hg (ofList d3RA)) := by
  refine Chk.run_sound (chkSound hn (by norm_num) g hg (fun f hf => d3At_three le_rfl _ _) ?_) chA runA
  intro p hp
  simp only [e20A, List.mem_singleton] at hp
  subst hp
  exact e20_gb hn g hg _ _ _ (by decide) (by decide)

/-- (d3) at `0, 2, 1, 3` moved along any increasing `g`. -/
theorem gb_d3B (hn : 3 ≤ n) (g : Fin 4 → Fin (2 ^ n)) (hg : StrictMono g) :
    GB n (wmap g hg (ofList d3LB)) (wmap g hg (ofList d3RB)) := by
  refine Chk.run_sound (chkSound hn (by norm_num) g hg (fun f hf => d3At_three le_rfl _ _) ?_) chB runB
  intro p hp
  simp only [e20B, List.mem_singleton] at hp
  subst hp
  exact e20_gb hn g hg _ _ _ (by decide) (by decide)

theorem vec4_mono {N : ℕ} {a b c d : Fin N} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    StrictMono ![a, b, c, d] := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

/-- Figure 6's (d3) is in `GB`. -/
theorem gb_d3 (hn : 3 ≤ n) {a b c d : Fin (2 ^ n)} (hab : a < b) (hcd : c < d) (hac : a < c)
    (hbd : b < d) (hbc : b ≠ c) :
    GB n ((H_[c,d] * H_[a,c] * H_[b,d]) ^ 4) (H_[a,b] * H_[c,d]) := by
  rcases lt_or_gt_of_ne hbc with h | h
  · have k := gb_d3A hn _ (vec4_mono hab h hcd)
    have e1 : wmap ![a, b, c, d] (vec4_mono hab h hcd) (ofList d3LA) =
        (H_[c,d] * H_[a,c] * H_[b,d]) ^ 4 := by
      rw [wmap_ofList]; apply FreeMonoid.toList.injective
      simp only [d3LA, List.map_cons, List.map_nil, FreeMonoid.toList_ofList, pow_succ, pow_zero,
        one_mul, FreeMonoid.toList_mul, FreeMonoid.toList_of, HadamardPi.Gen.map, hL,
        List.cons_append, List.nil_append, List.singleton_append]
      all_goals rfl
    have e2 : wmap ![a, b, c, d] (vec4_mono hab h hcd) (ofList d3RA) = H_[a,b] * H_[c,d] := by
      rw [wmap_ofList]; apply FreeMonoid.toList.injective
      simp only [d3RA, List.map_cons, List.map_nil, FreeMonoid.toList_ofList, FreeMonoid.toList_mul,
        FreeMonoid.toList_of, HadamardPi.Gen.map, hL, List.cons_append, List.nil_append,
        List.singleton_append]
      all_goals rfl
    rwa [e1, e2] at k
  · have k := gb_d3B hn _ (vec4_mono hac h hbd)
    have e1 : wmap ![a, c, b, d] (vec4_mono hac h hbd) (ofList d3LB) =
        (H_[c,d] * H_[a,c] * H_[b,d]) ^ 4 := by
      rw [wmap_ofList]; apply FreeMonoid.toList.injective
      simp only [d3LB, List.map_cons, List.map_nil, FreeMonoid.toList_ofList, pow_succ, pow_zero,
        one_mul, FreeMonoid.toList_mul, FreeMonoid.toList_of, HadamardPi.Gen.map, hL,
        List.cons_append, List.nil_append, List.singleton_append]
      all_goals rfl
    have e2 : wmap ![a, c, b, d] (vec4_mono hac h hbd) (ofList d3RB) = H_[a,b] * H_[c,d] := by
      rw [wmap_ofList]; apply FreeMonoid.toList.injective
      simp only [d3RB, List.map_cons, List.map_nil, FreeMonoid.toList_ofList, FreeMonoid.toList_mul,
        FreeMonoid.toList_of, HadamardPi.Gen.map, hL, List.cons_append, List.nil_append,
        List.singleton_append]
      all_goals rfl
    rwa [e1, e2] at k

/-- (d3) moved along any increasing `g`. -/
theorem d3At_all (hn : 3 ≤ n) {k : ℕ} (g : Fin k → Fin (2 ^ n)) (hg : StrictMono g) :
    D3At n g hg := by
  intro a b c d hab hcd hac hbd hbc
  have := gb_d3 hn (hg hab) (hg hcd) (hg hac) (hg hbd) (fun e => hbc (hg.injective e))
  simpa only [map_pow, map_mul, wmap, FreeMonoid.map_of, HadamardPi.Gen.map] using this

end QCert.RealCliffordCH.Sec8
