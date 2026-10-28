/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: Theorem 4.10

By the Reidemeister–Schreier theorem for monoids (`Sec8/A/RS.lean`):
Theorem 4.10 follows from its hypotheses (a) (`ItemA`, the equations
(DE-**) of Appendix A.3.2) and (b) (`ItemB`, one equation per relation of
Figure 6 and coset), with the completeness of Figure 6
(`QCert.HadamardPi.theorem_4_14`). Hypothesis (a) is proved by the frame
construction in `A/ItemAProof`; hypothesis (b) remains open.
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Sec8.A.RS
import QCert.RealCliffordCH.Sec8.A.ItemAProof

namespace QCert.RealCliffordCH.Sec8

/-- Hypothesis (a) of the Reidemeister–Schreier theorem (Appendix A.3.2, the
equations (DE-**)). -/
theorem item_a (n : ℕ) (hn : 3 ≤ n) : ItemA n :=
  item_a_proof n hn

/-- Hypothesis (b) of the Reidemeister–Schreier theorem (Appendix A.3.2, one
equation per relation of Figure 6 and coset).  Not yet proved. -/
theorem item_b (n : ℕ) (hn : 3 ≤ n) : ItemB n := by
  sorry

/-- Theorem 4.10 (Appendices A.3 and A.4). -/
theorem theorem_4_10 (n : ℕ) (hn : 3 ≤ n) : Thm410 n :=
  thm410_of (item_a n hn) (item_b n hn)

end QCert.RealCliffordCH.Sec8
