/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The spectator sign for the restricted coset calculation
-/
import QCert.CliffordCS3.Three.PhasePoint
import QCert.CliffordCS3.Three.PhaseOuter

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhaseGaugeSupport

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed PhaseOuter
noncomputable section

theorem C_token4 : Commute C (u (Cert.token 4)) := by
  have h := PhaseStabilizers.phase_token3.map sw
  have he : sw (u (Cert.token 3)) = u (Cert.token 4) := by
    have h3 : u (Cert.token 3) = F2 * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * F2 := by
      rw [← K_inv 1]; rfl
    rw [h3]
    simp only [map_mul, map_inv, sw_F2, sw_K, sw_Q]
    rw [← K_inv 0]
    rfl
  rwa [sw_P, he] at h

theorem F1_C : Commute F1 C := by
  have hk := WhiteSign.c_K1_commute
  have hs := PhaseStabilizers.S1_C.symm
  have hi : Commute C (u W.I) := by
    have hh : sw (u W.I) = u W.I := sw_I
    have h : Commute P (u W.I) :=
      of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
    have ht := h.map sw
    rwa [sw_P, hh] at ht
  simpa only [F1, W.X, map_mul] using
    ((((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi).symm

theorem C_token2 : Commute C (u (Cert.token 2)) := by
  have h := C_token4.conj F1
  rw [Monomial.inv_of_square F1_square] at h
  have he : F1 * C * F1 = C := by
    rw [F1_C.eq, mul_assoc, F1_square, mul_one]
  rw [he] at h
  exact h

theorem C_token1 : Commute C (u (Cert.token 1)) := by
  have h := C_token5.conj F1
  rw [Monomial.inv_of_square F1_square] at h
  have he : F1 * C * F1 = C := by
    rw [F1_C.eq, mul_assoc, F1_square, mul_one]
  rw [he] at h
  have hf : Commute F1 F0 :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Xu) (v := Two.W2.Xu * Two.W2.Xl)
      (by decide +kernel)))
  have ht : F1 * u (Cert.token 5) * F1 = u (Cert.token 1) := by
    rw [token5_form]
    calc
      F1 * (F0 * U2 * F0) * F1 = (F1 * F0) * U2 * (F0 * F1) := by group
      _ = (F0 * F1) * U2 * (F1 * F0) := by rw [hf.eq, hf.symm.eq]
      _ = u (Cert.token 1) := by rw [U2, ← K_inv 2]; rfl
  rwa [ht] at h

abbrev r : G := C ^ 2 * Q

theorem r_Q : Commute r Q := (C_Q.pow_left 2).mul_left (Commute.refl Q)

theorem A_inv_short : A⁻¹ = A ^ 2 * P ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_right
  calc
    A * (A ^ 2 * P ^ 2) = A ^ 3 * P ^ 2 := by group
    _ = P ^ 2 * P ^ 2 := by rw [A_cube]
    _ = 1 := by simpa only [← pow_add] using P_fourth

theorem QAQ : Q * A * Q = P ^ 3 * A ^ 2 * Q * A ^ 2 := by
  have h : Q * A * Q = P ^ 3 * A⁻¹ * Q * A⁻¹ := by
    have hi := Monomial.inv_of_square Q_square
    calc
      Q * A * Q = (Q * A) ^ 3 * A⁻¹ * Q⁻¹ * A⁻¹ := by
        simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
          mul_inv_cancel_left, mul_inv_cancel]
      _ = P ^ 3 * A⁻¹ * Q * A⁻¹ := by rw [QA_cube, hi]
  rw [h, A_inv_short]
  have hp : Commute (P ^ 2) (Q * A ^ 2) := (P_Q.mul_right (P_A.pow_right 2)).pow_left 2
  calc
    P ^ 3 * (A ^ 2 * P ^ 2) * Q * (A ^ 2 * P ^ 2) =
        (P ^ 3 * A ^ 2) * (P ^ 2 * (Q * A ^ 2)) * P ^ 2 := by group
    _ = (P ^ 3 * A ^ 2) * ((Q * A ^ 2) * P ^ 2) * P ^ 2 := by rw [hp.eq]
    _ = (P ^ 3 * A ^ 2 * Q * A ^ 2) * P ^ 4 := by group
    _ = _ := by rw [P_fourth, mul_one]

theorem C2_A : C ^ 2 * A * (C ^ 2)⁻¹ = Q * A * Q := by
  let f : G →* G := (MulAut.conj C).toMonoidHom
  have ha : f A = A ^ 2 * P * Q := PhasePoint.C_atom_dresses
  have hp : f P = P := by
    change C * P * C⁻¹ = P
    have hc : Commute C P := Monomial.c_b_commute
    rw [hc.eq]; group
  have hq : f Q = Q := by
    change C * Q * C⁻¹ = Q
    rw [C_Q.eq]; group
  have he : C ^ 2 * A * (C ^ 2)⁻¹ = (A ^ 2 * P * Q) ^ 2 * P * Q := by
    calc
      C ^ 2 * A * (C ^ 2)⁻¹ = f (f A) := by
        simp only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sq]; group
      _ = _ := by rw [ha, map_mul, map_mul, map_pow, ha, hp, hq]
  have hpa : Commute P (A ^ 2 * Q) := (P_A.pow_right 2).mul_right P_Q
  have hbase : A ^ 2 * P * Q = P * (A ^ 2 * Q) := by
    rw [(P_A.pow_right 2).symm.eq, mul_assoc]
  rw [he, hbase, hpa.mul_pow]
  calc
    P ^ 2 * (A ^ 2 * Q) ^ 2 * P * Q =
        P ^ 2 * P * ((A ^ 2 * Q) ^ 2 * Q) := by
      rw [mul_assoc (P ^ 2), (hpa.pow_right 2).symm.eq]
      group
    _ = P ^ 3 * (A ^ 2 * Q * A ^ 2) := by
      rw [pow_two (A ^ 2 * Q)]
      simp only [mul_assoc, Q_square, mul_one]
      group
    _ = Q * A * Q := by rw [QAQ]; group

theorem r_A : Commute r A := by
  have hi := Monomial.inv_of_square Q_square
  have he : r * A * r⁻¹ = A := by
    change (C ^ 2 * Q) * A * (C ^ 2 * Q)⁻¹ = A
    rw [mul_inv_rev, hi]
    have hc := C_Q.pow_left 2
    calc
      (C ^ 2 * Q) * A * (Q * (C ^ 2)⁻¹) =
          Q * (C ^ 2 * A * (C ^ 2)⁻¹) * Q := by
        rw [hc.eq, hc.inv_left.symm.eq]
        group
      _ = Q * (Q * A * Q) * Q := by rw [C2_A]
      _ = A := by simp only [mul_assoc, show ∀ x : G, Q * (Q * x) = x from
          fun x => by rw [← mul_assoc, Q_square, one_mul], Q_square, mul_one]
  change r * A = A * r
  have h := congrArg (fun x : G => x * r) he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

theorem r_T : Commute r T := by
  have he : T = A * Q * A⁻¹ := by
    calc
      T = (T * A) * A⁻¹ := by group
      _ = A * Q * A⁻¹ := by rw [← A_Q]
  rw [he]
  exact (r_A.mul_right r_Q).mul_right r_A.inv_right

theorem r_token4 : Commute r (u (Cert.token 4)) :=
  (C_token4.pow_left 2).mul_left sign_token4

theorem r_token5 : Commute r (u (Cert.token 5)) :=
  (C_token5.pow_left 2).mul_left sign_token5

end
end QCert.CliffordCS3.Three.PhaseGaugeSupport
