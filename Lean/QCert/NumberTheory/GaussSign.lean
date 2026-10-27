/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The sign of the quadratic Gauss sum

Gauss's theorem: for an odd prime `p`,
`∑_{j mod p} e^{2πi j²/p} = √p` if `p ≡ 1 (mod 4)` and `i √p` if `p ≡ 3 (mod 4)`.
Mathlib has the square of the Gauss sum (`gaussSum_sq`) but not its sign.
The qudit Clifford rules (C2) and (C3) are sound exactly because of it.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

namespace QCert

open Complex in
/-- Gauss's evaluation of the quadratic Gauss sum. -/
theorem gauss_sum_sign (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ j : ZMod p, exp (2 * Real.pi * I * ((j.val ^ 2 : ℕ) : ℂ) / p) =
      if p % 4 = 1 then (Real.sqrt p : ℂ) else I * (Real.sqrt p : ℂ) := by
  sorry

end QCert
