/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: Lemma 8.7

Lemma 8.7 follows from Lemma 8.6 (Appendix E.4): the decoding of the
encoding of a circuit is the circuit, gate by gate (`E.lemma87_of`), each
gate case proved in `E/Lemma87Gates` (`Z`, `CZ`) and `E/Lemma87H` (`H`,
`CH`) from Lemma 8.4 (`E/Step84`) and the merges (309), (310) over all
colourings (`E/Merge`, `E/MergeHg`).
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Sec8.E.Lemma87H

namespace QCert.RealCliffordCH.Sec8

open Eng

/-- Lemma 8.7 (via Lemma 8.6, Appendix E.4). -/
theorem lemma_8_7 (n : ℕ) (hn : 3 ≤ n) : Lemma87 n := by
  intro ih
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 3 := ⟨n - 3, by omega⟩
  have ih' : IH (M + 3) := ih
  apply E.lemma87_of
  intro x hx hS
  cases x with
  | H j =>
    rcases j with _ | ℓ
    · exact E.lemma86_H_lo ih'
    · exact E.lemma86_H_hi ih' ℓ (by simp [L.lo, L.wd] at hx; omega)
  | Z j =>
    rcases j with _ | ℓ
    · exact E.lemma86_Z_lo ih'
    · exact E.lemma86_Z_hi ih' ℓ (by simp [L.lo, L.wd] at hx; omega)
  | C j =>
    rcases j with _ | ℓ
    · exact E.lemma86_CZ_lo ih'
    · exact E.lemma86_CZ_hi ih' ℓ (by simp [L.lo, L.wd] at hx; omega)
  | K j =>
    rcases j with _ | ℓ
    · exact E.lemma86_CH_lo ih'
    · exact E.lemma86_CH_hi ih' ℓ (by simp [L.lo, L.wd] at hx; omega)
  | S j => exact absurd rfl (hS j)

end QCert.RealCliffordCH.Sec8
