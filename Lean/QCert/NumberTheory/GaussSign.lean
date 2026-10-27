/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The sign of the quadratic Gauss sum

Gauss's theorem: for an odd prime `p`,
`∑_{j mod p} e^{2πi j²/p} = √p` if `p ≡ 1 (mod 4)` and `i √p` if `p ≡ 3 (mod 4)`.
Mathlib has the square of the Gauss sum (`gaussSum_sq`) but not its sign.
The qudit Clifford rules (C2) and (C3) are sound exactly because of it.

The proof is in `QCert.NumberTheory.GaussSumTheta`: the Landsberg–Schaar
identity at `q = 1`, from the functional equation of the Jacobi theta
function, gives `∑_{r < p} e^{2πir²/p} = √p (1 + i)/2 · (1 + e^{-πip/2})`
for every `p ≥ 1` (`GaussTheta.gauss_sum_fin`); here we read off the two
cases `p ≡ 1, 3 (mod 4)`.
-/
import QCert.NumberTheory.GaussSumTheta
import Mathlib.Data.ZMod.Basic

namespace QCert

open Complex in
/-- Gauss's evaluation of the quadratic Gauss sum. -/
theorem gauss_sum_sign (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ j : ZMod p, exp (2 * Real.pi * I * ((j.val ^ 2 : ℕ) : ℂ) / p) =
      if p % 4 = 1 then (Real.sqrt p : ℂ) else I * (Real.sqrt p : ℂ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp)
  have hsum : ∑ j : ZMod p, exp (2 * Real.pi * I * ((j.val ^ 2 : ℕ) : ℂ) / p) =
      ∑ r : Fin p, exp (2 * Real.pi * I * (r : ℂ) ^ 2 / p) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
    push_cast
    rfl
  rw [hsum, GaussTheta.gauss_sum_fin p hp0, GaussTheta.kappa]
  split_ifs with h4
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
    have : exp (-Real.pi * I * p / 2) = exp (-Real.pi / 2 * I) := by
      rw [exp_eq_exp_iff_exists_int]
      refine ⟨-k, ?_⟩
      rw [hk]; push_cast; ring
    rw [this, exp_neg_pi_div_two_mul_I]
    linear_combination (-(Real.sqrt p : ℂ) / 2) * I_sq
  · obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
    have : exp (-Real.pi * I * p / 2) = exp (Real.pi / 2 * I) := by
      rw [exp_eq_exp_iff_exists_int]
      refine ⟨-(k + 1), ?_⟩
      rw [hk]; push_cast; ring
    rw [this, exp_pi_div_two_mul_I]
    linear_combination ((Real.sqrt p : ℂ) / 2) * I_sq

end QCert
