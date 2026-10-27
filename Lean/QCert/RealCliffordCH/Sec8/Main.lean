/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: completeness from three wires on

Assembles the four statements of `Statement` into Theorem 8.9 for `n ≥ 3`.
-/
import QCert.RealCliffordCH.Sec8.ESemProof
import QCert.RealCliffordCH.Sec8.Thm410Proof
import QCert.RealCliffordCH.Sec8.Lemma87Proof
import QCert.RealCliffordCH.Sec8.Lemma88Proof

namespace QCert.RealCliffordCH.Sec8

/-- Theorem 8.9 on `n ≥ 3` wires, given completeness on fewer wires. -/
theorem complete_ge_three {n : ℕ} (hn : 3 ≤ n) (ih : ∀ k < n, CompleteAt k) : CompleteAt n :=
  complete_of (esem n hn) (theorem_4_10 n hn) (lemma_8_7 n hn) (lemma_8_8 n hn) ih

end QCert.RealCliffordCH.Sec8
