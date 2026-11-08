/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: Table 2's values

Translation of `TableMatrices.agda`: the values behind Table 2 of Li, Ross
and Selinger (`I ⊗ H = H₂`): for each relation `H g H = t`, `H₂`'s
conjugate (`Push.conj`) of the decoding of `g` has the value of the decoding
of `t`.  Checked by computing them.
-/
import QCert.ToffoliHadamardRS.Push
import QCert.ToffoliHadamardRS.DecMatrices

namespace QCert.ToffoliHadamardRS

noncomputable section

/-- The letters of Table 2, decoded. -/
abbrev M0 : Word G₁ := dec (mG 0)
abbrev M1 : Word G₁ := dec (mG 1)
abbrev M3 : Word G₁ := dec (mG 3)
abbrev M5 : Word G₁ := dec (mG 5)
abbrev M7 : Word G₁ := dec (mG 7)
abbrev X01 : Word G₁ := dec (xG 0 1)
abbrev X12 : Word G₁ := dec (xG 1 2)
abbrev X23 : Word G₁ := dec (xG 2 3)
abbrev X34 : Word G₁ := dec (xG 3 4)
abbrev X45 : Word G₁ := dec (xG 4 5)
abbrev X56 : Word G₁ := dec (xG 5 6)
abbrev X67 : Word G₁ := dec (xG 6 7)
abbrev K0123 : Word G₁ := dec (kG 0 1 2 3)
abbrev K2345 : Word G₁ := dec (kG 2 3 4 5)
abbrev K4567 : Word G₁ := dec (kG 4 5 6 7)

end

/-- (7b) -/
theorem t7b : sem₁ (conjW K0123) = sem₁ K0123 := semO_eq_of_check (by decide +kernel)

/-- (7c) -/
theorem t7c : sem₁ (conjW M0) = sem₁ (M0 * X01 * M0) := semO_eq_of_check (by decide +kernel)

/-- (7d), `x` even. -/
theorem t7d0 : sem₁ (conjW X01) = sem₁ M1 := semO_eq_of_check (by decide +kernel)
theorem t7d2 : sem₁ (conjW X23) = sem₁ M3 := semO_eq_of_check (by decide +kernel)
theorem t7d4 : sem₁ (conjW X45) = sem₁ M5 := semO_eq_of_check (by decide +kernel)
theorem t7d6 : sem₁ (conjW X67) = sem₁ M7 := semO_eq_of_check (by decide +kernel)

/-- (7d), `x` odd. -/
theorem t7d1 : sem₁ (conjW X12) = sem₁ (X12 * K0123) := semO_eq_of_check (by decide +kernel)
theorem t7d3 : sem₁ (conjW X34) = sem₁ (X34 * K2345) := semO_eq_of_check (by decide +kernel)
theorem t7d5 : sem₁ (conjW X56) = sem₁ (X56 * K4567) := semO_eq_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS
