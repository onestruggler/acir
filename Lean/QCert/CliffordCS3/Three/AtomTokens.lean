/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The atom commutes with transpositions on complementary controls
-/
import QCert.CliffordCS3.Three.LocalKZ
import QCert.CliffordCS3.Three.PhaseFlip
import QCert.CliffordCS3.Three.PhaseFlip2
import QCert.CliffordCS3.Three.Cert.AtomNegative
import QCert.CliffordCS3.Three.Cert.AtomWhite

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.AtomTokens

open QuotientGroup LocalKZ
noncomputable section

abbrev D : G := Monomial.dQ
abbrev F1 : G := u (W.X 1)
abbrev F2 : G := u (W.X 2)

theorem C_Q : Commute C Q := by
  rw [show Q = Monomial.cQ⁻¹ * (Monomial.aQ * Monomial.bQ * Monomial.aQ) *
    Monomial.bQ⁻¹ from Monomial.u_ccZ]
  exact (((Commute.refl C).inv_right).mul_right
    Monomial.c_conjugate_commute).mul_right Monomial.c_b_commute.inv_right

theorem D_Q : Commute D Q := of_derivable Monomial.CS01_ccZ_commute

theorem F1_K : Commute F1 K := by
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xl * Two.W2.Ku) (v := Two.W2.Ku * Two.W2.Xl)
    (by decide +kernel)))
  exact ht

theorem token0_form : u (Cert.token 0) = K * (Q * C ^ 2) * K⁻¹ := by
  have ht : u (Cert.token 0) = F1 * T * F1 := rfl
  have hflip : F1 * Q * F1 = Q * C ^ 2 := of_derivable Monomial.X1_ccZ_flip
  rw [ht, T_eq]
  calc
    F1 * (K * Q * K⁻¹) * F1 = K * (F1 * Q * F1) * K⁻¹ := by
      have h1 : F1 * (K * Q * K⁻¹) * F1 = (F1 * K) * Q * (K⁻¹ * F1) := by group
      rw [h1, F1_K.eq, F1_K.inv_right.symm.eq]
      group
    _ = _ := by rw [hflip]

theorem token4_form : u (Cert.token 4) = K * (Q * D ^ 2) * K⁻¹ := by
  have ht : u (Cert.token 4) = F2 * T * F2 := rfl
  have hflip : F2 * Q * F2 = Q * D ^ 2 := of_derivable Monomial.X2_ccZ
  have hk : Commute F2 K := Monomial.f2_K0_commute
  rw [ht, T_eq]
  calc
    F2 * (K * Q * K⁻¹) * F2 = K * (F2 * Q * F2) * K⁻¹ := by
      have h1 : F2 * (K * Q * K⁻¹) * F2 = (F2 * K) * Q * (K⁻¹ * F2) := by group
      rw [h1, hk.eq, hk.inv_right.symm.eq]
      group
    _ = _ := by rw [hflip]

theorem sw_D : sw D = D := of_derivable Swap01.conjugate_CS
theorem sw_P : sw P = C := rfl

theorem sw_I : sw (u W.I) = u W.I := of_derivable Swap01.conjugate_I

theorem IK : u W.I * K = K⁻¹ := by simpa only [map_mul] using K_inv 0

theorem cancel_phase_commute {B : G} (hab : Commute A (P * B)) : Commute A B := by
  apply mul_left_cancel (a := P)
  calc
    P * (A * B) = A * (P * B) := by rw [← mul_assoc, P_A.eq, mul_assoc]
    _ = P * B * A := hab.eq
    _ = P * (B * A) := by group

theorem atom_token0 : Commute A (u (Cert.token 0)) := by
  have ht := congrArg sw (of_derivable Cert.AtomNegative.comm_negA)
  change sw (AM * (u (W.K 1) * P ^ 2 * R * u (W.I * W.K 1))) =
    sw ((u (W.K 1) * P ^ 2 * R * u (W.I * W.K 1)) * AM) at ht
  simp only [map_mul, map_pow, sw_A, sw_K, sw_P, sw_R, sw_I, IK] at ht
  have hCP : Commute C P := Monomial.c_b_commute
  have he : K * C ^ 2 * (P * Q) * K⁻¹ = P * u (Cert.token 0) := by
    rw [token0_form]
    calc
      K * C ^ 2 * (P * Q) * K⁻¹ = K * (C ^ 2 * P) * Q * K⁻¹ := by group
      _ = K * (P * C ^ 2) * Q * K⁻¹ := by rw [(hCP.pow_left 2).eq]
      _ = (K * P) * (C ^ 2 * Q) * K⁻¹ := by group
      _ = (P * K) * (Q * C ^ 2) * K⁻¹ := by rw [P_K.symm.eq, (C_Q.pow_left 2).eq]
      _ = _ := by group
  rw [he] at ht
  exact cancel_phase_commute ht

theorem atom_token4 : Commute A (u (Cert.token 4)) := by
  have ht := congrArg sw (of_derivable Cert.AtomNegative.comm_negB)
  change sw (AM * (u (W.K 1) * D ^ 2 * R * u (W.I * W.K 1))) =
    sw ((u (W.K 1) * D ^ 2 * R * u (W.I * W.K 1)) * AM) at ht
  simp only [map_mul, map_pow, sw_A, sw_K, sw_D, sw_R, sw_I, IK] at ht
  have hDP : Commute D P := Monomial.b_d_commute.symm
  have he : K * D ^ 2 * (P * Q) * K⁻¹ = P * u (Cert.token 4) := by
    rw [token4_form]
    calc
      K * D ^ 2 * (P * Q) * K⁻¹ = K * (D ^ 2 * P) * Q * K⁻¹ := by group
      _ = K * (P * D ^ 2) * Q * K⁻¹ := by rw [(hDP.pow_left 2).eq]
      _ = (K * P) * (D ^ 2 * Q) * K⁻¹ := by group
      _ = (P * K) * (Q * D ^ 2) * K⁻¹ := by rw [P_K.symm.eq, (D_Q.pow_left 2).eq]
      _ = _ := by group
  rw [he] at ht
  exact cancel_phase_commute ht

end
end QCert.CliffordCS3.Three.AtomTokens
