/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The phase at the next basis state commutes with the Hadamard block
-/
import QCert.CliffordCS3.Three.PhaseGaugeSupport

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PointCommutation

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed PhaseOuter
noncomputable section

abbrev V : G := u (Cert.token 5)
def E : G := S1 * C * D⁻¹ * P⁻¹

theorem F0_P : F0 * P * F0 = P := by
  simpa only [Monomial.conj0_eq] using Monomial.conj0_b

theorem F0_Q : F0 * Q * F0 = Q * P ^ 2 := by
  simpa only [Monomial.conj0_eq] using Monomial.conj0_ccZ

theorem V_P : V * P * V = S1 * D⁻¹ * P⁻¹ * Q := by
  let f : G →* G := (MulAut.conj F0).toMonoidHom
  have hf (x : G) : f x = F0 * x * F0 := by
    change F0 * x * F0⁻¹ = _
    rw [Monomial.inv_of_square Monomial.flip0_square]
  have ht := congrArg f U2_P
  have hv : f U2 = V := by rw [hf]; exact token5_form.symm
  have hp : f P = P := by rw [hf]; exact F0_P
  have hd : f D = D⁻¹ * S1 := by rw [hf]; exact F0_D
  have hq : f Q = Q * P ^ 2 := by rw [hf]; exact F0_Q
  simp only [map_mul, hv, hp, hd, hq] at ht
  have hsD : Commute S1 D := of_derivable (Derivable.of (Rel.c7 0))
  have hsP : Commute S1 P := of_derivable (Derivable.of (Rel.c6 1))
  have hDP : Commute D P := Monomial.b_d_commute.symm
  rw [ht]
  calc
    P * (D⁻¹ * S1) * (Q * P ^ 2) = (P * D⁻¹) * S1 * ((P ^ 2) * Q) := by
      rw [(P_Q.pow_left 2).symm.eq]; group
    _ = (D⁻¹ * P) * S1 * ((P ^ 2) * Q) := by rw [hDP.inv_left.symm.eq]
    _ = D⁻¹ * S1 * P ^ 3 * Q := by rw [mul_assoc D⁻¹ P S1, hsP.symm.eq]; group
    _ = S1 * D⁻¹ * P⁻¹ * Q := by
      rw [hsD.inv_right.symm.eq, Monomial.cube_eq_inv P_fourth]

theorem T_C : T * C * T = C * P * Q := by
  have ht := congrArg sw12 T_D
  have hd : sw12 D = C := by rw [sw12_eq]; exact Monomial.swap12_d
  simpa only [map_mul, sw12_T, hd, sw12_P, sw12_Q] using ht

theorem frame_phase : V * T * C * T * V = E := by
  have hv := token_square_G 5
  have hi := Monomial.inv_of_square hv
  have hc : Commute V C := C_token5.symm
  have hq : Commute V Q := sign_token5.symm
  have he : V * C * V = C := by rw [hc.eq, mul_assoc, hv, mul_one]
  have heq : V * Q * V = Q := by rw [hq.eq, mul_assoc, hv, mul_one]
  calc
    V * T * C * T * V = V * (T * C * T) * V := by group
    _ = V * (C * P * Q) * V := by rw [T_C]
    _ = (V * C * V) * (V * P * V) * (V * Q * V) := by
      have h : V * (C * P * Q) * V⁻¹ =
          (V * C * V⁻¹) * (V * P * V⁻¹) * (V * Q * V⁻¹) := by group
      simpa only [hi] using h
    _ = C * (S1 * D⁻¹ * P⁻¹ * Q) * Q := by rw [he, V_P, heq]
    _ = E := by
      simp only [mul_assoc, Q_square, mul_one]
      rw [← mul_assoc, PhaseStabilizers.S1_C.symm.eq]
      rfl

theorem S1_A : Commute S1 A := by
  have hk : Commute S1 K :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 0 1 (by decide))).symm
  have hd : Commute S1 D := of_derivable (Derivable.of (Rel.c7 0))
  have hc := PhaseStabilizers.S1_C
  rw [AtomControlSymmetry.A_form]
  exact ((((((hk.mul_right hd).mul_right hk.inv_right).mul_right hc.inv_right).mul_right
    hk).mul_right hd.inv_right).mul_right hk.inv_right).mul_right hc

theorem CD_A : Commute (C * D⁻¹) A := by
  have he : C * A * C⁻¹ = D * A * D⁻¹ := by
    rw [PhasePoint.C_atom_dresses, PhasePoint.D_atom_dresses]
  have hd : Commute C D := Monomial.c_d_commute
  have hh : (D⁻¹ * C) * A * (D⁻¹ * C)⁻¹ = A := by
    calc
      (D⁻¹ * C) * A * (D⁻¹ * C)⁻¹ = D⁻¹ * (C * A * C⁻¹) * D := by group
      _ = D⁻¹ * (D * A * D⁻¹) * D := by rw [he]
      _ = A := by group
  have h := congrArg (fun x : G => x * (D⁻¹ * C)) hh
  simp only [mul_assoc, inv_mul_cancel, mul_one] at h
  change Commute (D⁻¹ * C) A at h
  rwa [hd.inv_right.symm.eq] at h

theorem E_A : Commute E A := by
  have h := (S1_A.mul_left CD_A).mul_left P_A.inv_left
  simpa only [E, mul_assoc] using h

theorem E_C : Commute E C := by
  exact (((PhaseStabilizers.S1_C.mul_left (Commute.refl C)).mul_left
    Monomial.c_d_commute.symm.inv_left).mul_left Monomial.c_b_commute.symm.inv_left)

theorem point_block : Commute (V * T * C * T * V) (A * C) := by
  rw [frame_phase]
  exact E_A.mul_right E_C

end
end QCert.CliffordCS3.Three.PointCommutation
