/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A phase outside the residual Hadamard block
-/
import QCert.CliffordCS3.Three.PhaseStabilizers
import QCert.CliffordCS3.Three.Cert.PhasePoint
import QCert.CliffordCS3.Three.AtomControlSymmetry

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhasePoint

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed
noncomputable section

theorem D_atom_dresses : D * A * D⁻¹ = A ^ 2 * P * Q := by
  have ht := congrArg sw (of_derivable Cert.PhasePoint.point_false)
  simp only [map_mul, map_pow, sw_D, sw_A, sw_R, sw_phaseSquare] at ht
  change D ^ 3 * A ^ 2 * P ^ 2 = A * D ^ 3 * (P * Q) at ht
  rw [Monomial.cube_eq_inv Monomial.d_fourth] at ht
  have hDP : Commute D P := Monomial.b_d_commute.symm
  have hDQ : Commute D Q := D_Q
  have hPDQ : Commute D⁻¹ (P * Q) := (hDP.mul_right hDQ).inv_left
  have he : D⁻¹ * A ^ 2 * D * P ^ 2 = A * (P * Q) := by
    calc
      D⁻¹ * A ^ 2 * D * P ^ 2 = (D⁻¹ * A ^ 2 * P ^ 2) * D := by
        rw [mul_assoc _ D, (hDP.pow_right 2).eq]
        group
      _ = (A * D⁻¹ * (P * Q)) * D := by rw [ht]
      _ = A * (P * Q) := by rw [mul_assoc A D⁻¹, hPDQ.eq]; group
  have hi : (P ^ 2)⁻¹ = P ^ 2 := by
    apply Monomial.inv_of_square
    simpa only [← pow_add] using P_fourth
  have hmid : D⁻¹ * A ^ 2 * D = A * P ^ 3 * Q := by
    have hh := congrArg (fun x : G => x * (P ^ 2)⁻¹) he
    simp only [mul_assoc, mul_inv_cancel, mul_one] at hh
    rw [hi] at hh
    calc
      D⁻¹ * A ^ 2 * D = A * (P * Q) * P ^ 2 := hh
      _ = A * P ^ 3 * Q := by rw [mul_assoc A (P * Q),
        mul_assoc P Q, (P_Q.pow_left 2).symm.eq]; group
  have h := congrArg (fun x : G => D * x * D⁻¹) hmid
  have hDPQ : Commute D (P ^ 3 * Q) := (hDP.pow_right 3).mul_right hDQ
  have hh : A ^ 2 = (D * A * D⁻¹) * (P ^ 3 * Q) := by
    calc
      A ^ 2 = D * (D⁻¹ * A ^ 2 * D) * D⁻¹ := by group
      _ = D * (A * P ^ 3 * Q) * D⁻¹ := h
      _ = (D * A * D⁻¹) * (P ^ 3 * Q) := by
        calc
          D * (A * P ^ 3 * Q) * D⁻¹ = (D * A) * ((P ^ 3 * Q) * D⁻¹) := by group
          _ = (D * A) * (D⁻¹ * (P ^ 3 * Q)) := by rw [hDPQ.inv_left.symm.eq]
          _ = _ := by group
  calc
    D * A * D⁻¹ = A ^ 2 * (P ^ 3 * Q)⁻¹ := by rw [hh]; group
    _ = A ^ 2 * P * Q := by
      rw [mul_inv_rev, Monomial.inv_of_square Q_square,
        Monomial.cube_eq_inv P_fourth, inv_inv, P_Q.symm.eq]
      group

theorem C_atom_dresses : C * A * C⁻¹ = A ^ 2 * P * Q := by
  have h := congrArg AtomControlSymmetry.f12 D_atom_dresses
  have hp : AtomControlSymmetry.f12 P = P := sw12_P
  simpa only [map_mul, map_pow, map_inv, AtomControlSymmetry.f12_D,
    AtomControlSymmetry.f12_A, AtomControlSymmetry.f12_Q, hp] using h

end
end QCert.CliffordCS3.Three.PhasePoint
