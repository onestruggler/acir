/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Swapping the outer controls in the phase calculus
-/
import QCert.CliffordCS3.Three.PhaseStabilizers

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhaseOuter

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed
noncomputable section

theorem sw_K2 : sw K2 = K2 := by
  have hk1 : Commute K2 (u (W.K 1)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 1 2 (by decide))).symm
  have hk0 : Commute K2 K :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 2 (by decide))).symm
  have hd : Commute K2 D :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.K))
  have hi : Commute K2 (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .K₂ (by decide))).symm
  have ha : Commute K2 Monomial.aQ := by
    simpa only [Monomial.aQ, W.CX01, W.CX, map_mul] using
      (((hk1.mul_right hd).mul_right hd).mul_right hk1).mul_right hi
  have hx : Commute K2 Monomial.xQ := by
    simpa only [Monomial.xQ, W.CX10, W.CX, map_mul] using
      (((hk0.mul_right hd).mul_right hd).mul_right hk0).mul_right hi
  have hs : Commute K2 S := (ha.mul_right hx).mul_right ha
  change S * K2 * S = K2
  rw [hs.symm.eq, mul_assoc, S_square, mul_one]

def outer : G →* G := sw.comp (sw12.comp sw)

theorem outer_K : outer K = K2 := by
  simp only [outer, MonoidHom.comp_apply, sw_K0, sw12_K1, sw_K2]

theorem outer_Q : outer Q = Q := by
  simp only [outer, MonoidHom.comp_apply, sw_Q, sw12_Q]

theorem outer_D : outer D = P := by
  simp only [outer, MonoidHom.comp_apply, sw_D]
  have h : sw12 D = C := by rw [sw12_eq]; exact Monomial.swap12_d
  rw [h, sw_C]

theorem outer_P : outer P = D := by
  simp only [outer, MonoidHom.comp_apply, sw_P, sw12_C, sw_D]

theorem outer_T : outer T = U2 := by
  rw [T_eq]
  simp only [map_mul, map_inv, outer_K, outer_Q]

theorem token_square_G (i : Fin 7) : u (Cert.token i) * u (Cert.token i) = 1 := by
  simpa only [map_mul, map_one] using of_derivable (token_square Monomial.ccZ_square i)

theorem T_D : T * D * T = D * P * Q := by
  have ht := D_dresses
  have hp : Commute P T := (of_derivable Monomial.phase_token6_commute).symm
  have hP : Commute D P := Monomial.b_d_commute.symm
  have he : D * T = P * T * Q * D := by
    have h := congrArg (fun x : G => x * D) ht
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  have hsq := token_square_G 6
  calc
    T * D * T = T * (P * T * Q * D) := by rw [mul_assoc, he]
    _ = P * Q * D := by
      calc
        T * (P * T * Q * D) = (T * P) * T * Q * D := by group
        _ = (P * T) * T * Q * D := by rw [hp.symm.eq]
        _ = P * Q * D := by rw [mul_assoc P T T, hsq, mul_one]
    _ = D * P * Q := by rw [(hP.mul_right D_Q).symm.eq]; group

theorem U2_P : U2 * P * U2 = P * D * Q := by
  have h := congrArg outer T_D
  simpa only [map_mul, outer_T, outer_D, outer_P, outer_Q] using h

theorem C_token5 : Commute C (u (Cert.token 5)) := by
  have h := PhaseStabilizers.phase_token3.map (sw.comp sw12)
  have he : (sw.comp sw12) (u (Cert.token 3)) = u (Cert.token 5) := by
    have h3 : u (Cert.token 3) = F2 * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * F2 := by
      rw [← K_inv 1]
      rfl
    rw [h3]
    simp only [MonoidHom.comp_apply, map_mul, map_inv, sw12_F2, sw12_K1, sw12_Q,
      sw_F1, sw_K2, sw_Q]
    rw [← K_inv 2]
    rfl
  rw [he] at h
  simpa only [MonoidHom.comp_apply, sw12_P, sw_P] using h

end
end QCert.CliffordCS3.Three.PhaseOuter
