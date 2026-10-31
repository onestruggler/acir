/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symmetry of the controlled sign under the first adjacent swap

The expression for CCZ is symmetric in its first two Boolean controls.
This follows algebraically from the commuting phase equations established
in Monomial, without assuming completeness on three qubits.
-/
import QCert.CliffordCS3.Three.Monomial

namespace QCert.CliffordCS3.Three.Monomial

open QuotientGroup
noncomputable section

theorem swap_conjugates_a : swapQ * aQ * swapQ = xQ := by
  have haa (z : G) : aQ * (aQ * z) = z := by rw [← mul_assoc, a_square, one_mul]
  have hxx (z : G) : xQ * (xQ * z) = z := by rw [← mul_assoc, x_square, one_mul]
  change (aQ * xQ * aQ) * aQ * (aQ * xQ * aQ) = xQ
  calc
    (aQ * xQ * aQ) * aQ * (aQ * xQ * aQ) = aQ * xQ * aQ * xQ * aQ := by
      simp only [mul_assoc, haa]
    _ = xQ * aQ * xQ * xQ * aQ := by rw [cnot_braid]
    _ = xQ := by simp only [mul_assoc, hxx, a_square, mul_one]

theorem swap_conjugates_conjugate :
    swapQ * (aQ * bQ * aQ) * swapQ = aQ * bQ * aQ := by
  have hs := inv_of_square swap_square
  calc
    swapQ * (aQ * bQ * aQ) * swapQ =
        (swapQ * aQ * swapQ) * (swapQ * bQ * swapQ) * (swapQ * aQ * swapQ) := by
      have ht : swapQ * (aQ * bQ * aQ) * swapQ⁻¹ =
          (swapQ * aQ * swapQ⁻¹) * (swapQ * bQ * swapQ⁻¹) *
            (swapQ * aQ * swapQ⁻¹) := by group
      simpa only [hs] using ht
    _ = xQ * cQ * xQ := by rw [swap_conjugates_a]; rfl
    _ = aQ * bQ * aQ := by
      rw [c_as_conjugate]
      have hxx (z : G) : xQ * (xQ * z) = z := by rw [← mul_assoc, x_square, one_mul]
      simp only [mul_assoc, hxx, x_square, mul_one]

theorem c_conjugate_commute : Commute cQ (aQ * bQ * aQ) := by
  have hca : Commute cQ aQ := c_as_conjugate ▸
    commute_third_phase_cnot a_square x_square cnot_braid b_x_commute
  exact (hca.mul_right c_b_commute).mul_right hca

theorem swap_ccZ : Derivable Rel (swapWord * Cert.ccZ * swapWord) Cert.ccZ := by
  apply to_derivable
  simp only [map_mul, u_ccZ]
  have hs := inv_of_square swap_square
  have hsc : swapQ * cQ * swapQ = bQ := by
    rw [cQ]
    have hss (z : G) : swapQ * (swapQ * z) = z := by
      rw [← mul_assoc, swap_square, one_mul]
    simp only [mul_assoc, hss, swap_square, mul_one]
  calc
    swapQ * (cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹) * swapQ =
        (swapQ * cQ * swapQ)⁻¹ * (swapQ * (aQ * bQ * aQ) * swapQ) *
          (swapQ * bQ * swapQ)⁻¹ := by
      have ht : swapQ * (cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹) * swapQ⁻¹ =
          (swapQ * cQ * swapQ⁻¹)⁻¹ * (swapQ * (aQ * bQ * aQ) * swapQ⁻¹) *
            (swapQ * bQ * swapQ⁻¹)⁻¹ := by group
      simpa only [hs] using ht
    _ = bQ⁻¹ * (aQ * bQ * aQ) * cQ⁻¹ := by
      rw [hsc, swap_conjugates_conjugate]; rfl
    _ = cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹ := by
      have hb := b_conjugate_commute.inv_left
      have hc := c_conjugate_commute.inv_left
      rw [hb.eq, mul_assoc, c_b_commute.inv_inv.symm.eq, ← mul_assoc, hc.symm.eq]

end
end QCert.CliffordCS3.Three.Monomial
