/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: soundness

Translation of `Soundness.agda`.  Soundness in `O(8, 𝔻)`: every relation of
Figure 4 (`R₀`), of Figure 7 (`R₈₄`) and `r_K` holds for the values.  Both
sides are closed words, compared by computing their values, each comparison
one Boolean (`Decide`); Figure 7's, the costly ones, are lemmas in
`Soundness/Figure7a` and `Figure7b`.

The Agda states these at every level `k`.  `decide` does not accept a
statement with a free level, so here they are stated at the levels at which
they are used: Figure 4 at levels `0`, `1`, `2`, Figure 7 and `r_K` at
levels `1`, `2` (`k ≤ 2`, resp. `k ≤ 1` for `Gate (k + 1)`).
-/
import QCert.ToffoliHadamardRS.Soundness.Figure7a
import QCert.ToffoliHadamardRS.Soundness.Figure7b
import Mathlib.Tactic.IntervalCases

namespace QCert.ToffoliHadamardRS

open Soundness.Figure7a Soundness.Figure7b

/-- Figure 4. -/
theorem sound0 {k : ℕ} (hk : k ≤ 2) {w v : Word (Gate k)} (h : R0 w v) : semO w = semO v := by
  interval_cases k <;> cases h <;> exact semO_eq_of_check (by decide +kernel)

/-- Figure 7. -/
theorem sound7 {k : ℕ} (hk : k ≤ 1) {w v : Word (Gate (k + 1))} (h : Fig7 w v) :
    semO w = semO v := by
  interval_cases k
  · cases h
    exacts [s83, s84, s85, s86, s87, s88, s89, s90, s91, s92, s93, s94, s95, s96, s97, s98, s99, s100, s101]
  · cases h
    exacts [s83', s84', s85', s86', s87', s88', s89', s90', s91', s92', s93', s94', s95', s96', s97', s98', s99', s100', s101']

/-- `r_K`. -/
theorem soundK {k : ℕ} (hk : k ≤ 1) {w v : Word (Gate (k + 1))} (h : RK w v) :
    semO w = semO v := by
  interval_cases k
  · cases h; exact sK
  · cases h; exact sK'

end QCert.ToffoliHadamardRS
