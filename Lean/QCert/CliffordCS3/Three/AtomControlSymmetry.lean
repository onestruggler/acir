/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symmetry of the two controls of the residual atom
-/
import QCert.CliffordCS3.Three.AtomCross
import QCert.CliffordCS3.Three.PhaseStabilizers

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.AtomControlSymmetry

open QuotientGroup LocalKZ Monomial
noncomputable section

abbrev f12 : G →* G := PhaseCases.sw12

theorem f12_D : f12 dQ = C := by rw [PhaseCases.sw12_eq]; exact swap12_d

theorem f12_C : f12 C = dQ := PhaseDressed.sw12_C

theorem f12_Q : f12 Q = Q := PhaseCases.sw12_Q

theorem f12_K : f12 K = K := PhaseDressed.sw12_K0

theorem f12_X0 : f12 (u (W.X 0)) = u (W.X 0) := PhaseCases.sw12_F0

theorem f12_K1 : f12 (u (W.K 1)) = u (W.K 2) := PhaseCases.sw12_K1

theorem f12_X2 : f12 (u (W.X 2)) = u (W.X 1) := PhaseCases.sw12_F2
theorem A_form : A = K * dQ * K⁻¹ * C⁻¹ * K * dQ⁻¹ * K⁻¹ * C := by
  have hc4 : C ^ 4 = 1 := by
    have h := congrArg sw P_fourth
    simpa only [map_pow, map_one, AtomTokens.sw_P] using h
  have ht : A = K * dQ * (u W.I * K) * C ^ 3 * K * dQ ^ 3 * (u W.I * K) * C := by
    change u Cert.atom = _
    change u Cert.atom = K * dQ * (u W.I * K) * sw P ^ 3 * K * dQ ^ 3 * (u W.I * K) * sw P
    rw [← map_pow sw P 3]
    rfl
  rwa [show u W.I * K = K⁻¹ by simpa only [map_mul] using K_inv 0,
    cube_eq_inv hc4, cube_eq_inv d_fourth] at ht

theorem A_symmetric : A = K * C * K⁻¹ * dQ⁻¹ * K * C⁻¹ * K⁻¹ * dQ := by
  have ht := congrArg sw (of_derivable Cert.AtomFactor.symmetry)
  change sw AM = sw (u (W.K 1) * P * (u W.I * u (W.K 1)) * dQ ^ 3 *
    u (W.K 1) * P ^ 3 * (u W.I * u (W.K 1)) * dQ) at ht
  simp only [map_mul, map_pow, sw_A, sw_K, AtomTokens.sw_P, AtomTokens.sw_D,
    AtomTokens.sw_I, AtomTokens.IK] at ht
  have hc4 : C ^ 4 = 1 := by
    have h := congrArg sw P_fourth
    simpa only [map_pow, map_one, AtomTokens.sw_P] using h
  rwa [cube_eq_inv hc4, cube_eq_inv d_fourth] at ht

theorem f12_A : f12 A = A := by
  calc
    f12 A = f12 (K * dQ * K⁻¹ * C⁻¹ * K * dQ⁻¹ * K⁻¹ * C) := by rw [A_form]
    _ = K * C * K⁻¹ * dQ⁻¹ * K * C⁻¹ * K⁻¹ * dQ := by
      simp only [map_mul, map_inv, f12_K, f12_D, f12_C]
    _ = A := A_symmetric.symm

theorem f12_doublewhite :
    f12 (u (W.X 0) * u (Cert.token 3) * u (W.X 0)) = u (Cert.token 1) := by
  have t3 : u (Cert.token 3) = u (W.X 2) *
      (u (W.K 1) * Q * (u (W.K 1))⁻¹) * u (W.X 2) := by
    rw [← K_inv 1]
    rfl
  rw [t3]
  simp only [map_mul, map_inv, f12_X0, f12_X2, f12_K1, f12_Q]
  rw [← K_inv 2]
  rfl

end
end QCert.CliffordCS3.Three.AtomControlSymmetry

