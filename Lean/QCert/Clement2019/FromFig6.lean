/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The relations of Figure 6 hold in Clément's theory

Every relation (a1)–(d4) of Hadamard-Π's Figure 6, at every instance, is
derivable from Clément's relations once its generators are read as
Clément's (`fig6_rel`).  (a1)–(d2) are each one of (1)–(18), possibly read
backwards.  (d3) and (d4) are derived on four and six concrete indices
(`DerivedC.lean`, `kd3`, `kd4`: from (20) and (21) at their own indices,
with (19)), and moved to the indices of the instance by `derC_map`, which
needs (20) and (21) at other placements: those come from `Rel` by
conjugating with transpositions (`Conj.relK_rel`).
-/
import QCert.Clement2019.Conj
import QCert.Clement2019.DerivedC
import QCert.Clement2019.Translate

namespace QCert.Clement2019

open FreeMonoid
open HadamardPi (Fig6)

variable {n : ℕ}

set_option maxRecDepth 4000 in
/-- Each relation of Figure 6 holds in Clément's theory. -/
theorem fig6_rel {w v : Word (HadamardPi.Gen n)} (h : Fig6 w v) : Derivable Rel (ι w) (ι v) := by
  cases h with
  | a1 a => exact Derivable.of (Rel.r1 a)
  | a2 h => exact Derivable.of (Rel.r3 (ne_of_lt h))
  | a3 h => exact Derivable.of (Rel.r2 (ne_of_lt h))
  | b1 h => exact Derivable.of (Rel.r4 h)
  | b2 hbc hab hac => exact Derivable.of (Rel.r6 (ne_of_lt hbc) hab hac)
  | b3 hab hcd hac had hbc hbd =>
    exact Derivable.of (Rel.r9 (ne_of_lt hab) (ne_of_lt hcd) hac had hbc hbd)
  | b4 hbc hab hac => exact Derivable.of (Rel.r5 (ne_of_lt hbc) hab hac)
  | b5 hab hcd hac had hbc hbd =>
    exact (Derivable.of (Rel.r8 (ne_of_lt hcd) (ne_of_lt hab) (Ne.symm hac) (Ne.symm hbc)
      (Ne.symm had) (Ne.symm hbd))).symm
  | b6 hab hcd hac had hbc hbd =>
    exact Derivable.of (Rel.r7 (ne_of_lt hab) (ne_of_lt hcd) hac had hbc hbd)
  | c1 h => exact (Derivable.of (Rel.r10 (ne_of_lt h))).symm
  | c2 hab hbc =>
    exact (Derivable.of (Rel.r12 (ne_of_lt hab) (ne_of_lt (hab.trans hbc)) (ne_of_lt hbc))).symm
  | c3 hab hbc =>
    exact (Derivable.of (Rel.r13 (ne_of_lt hbc) (ne_of_gt hab) (ne_of_gt (hab.trans hbc)))).symm
  | c4 hab hbc =>
    exact (Derivable.of (Rel.r14 (ne_of_lt hab) (ne_of_lt (hab.trans hbc)) (ne_of_lt hbc))).symm
  | c5 hab hbc =>
    exact (Derivable.of (Rel.r15 (ne_of_lt hbc) (ne_of_gt hab) (ne_of_gt (hab.trans hbc)))).symm
  | d1 h => exact Derivable.of (Rel.r17 (ne_of_lt h))
  | d2 h => exact (Derivable.of (Rel.r18 (ne_of_lt h))).symm
  | @d3 a b c d hab hcd hac hbd hbc =>
    have hf : Function.Injective ![a, b, c, d] := by
      have : a < d := hac.trans hcd
      vec_inj
    have := relK_rel (derC_map ![a, b, c, d] hf kd3)
    simpa [ι, ofFig6, pow_succ, mul_assoc] using this
  | @d4 a b c d e f hac hbd hab hce hdf hef hbc hbe hcd hde =>
    have hf : Function.Injective ![a, b, c, d, e, f] := by
      have : a < d := hab.trans hbd
      have : a < e := hac.trans hce
      have : a < f := (hac.trans hce).trans hef
      have : b < f := hbd.trans hdf
      have : c < f := hce.trans hef
      have : d ≠ e := hde
      vec_inj
    have := relK_rel (derC_map ![a, b, c, d, e, f] hf kd4)
    simpa [ι, ofFig6, pow_succ, mul_assoc] using this

end QCert.Clement2019
