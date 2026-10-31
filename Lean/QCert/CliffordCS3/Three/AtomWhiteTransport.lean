/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The atom commutes with the transposition on two white controls
-/
import QCert.CliffordCS3.Three.AtomTokens

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.AtomTokens

open QuotientGroup LocalKZ
noncomputable section

abbrev S0 : G := u (W.S 0)

theorem S0_D : Commute S0 D := of_derivable (Derivable.of (Rel.c6 0))
theorem S0_C : Commute S0 C := Monomial.s0_c_commute

theorem S0_Q : Commute S0 Q := by
  change Commute S0 (u Cert.ccZ)
  rw [Monomial.u_ccZ]
  exact (S0_C.inv_right.mul_right Monomial.s0_D_commute).mul_right
    Monomial.s0_b_commute.inv_right

theorem F1_square : F1 * F1 = 1 := by
  simpa only [map_mul, map_one] using of_derivable (X_square 1)

def flip1 : G →* G where
  toFun x := F1 * x * F1⁻¹
  map_one' := by group
  map_mul' x y := by group

theorem flip1_Q : flip1 Q = Q * C ^ 2 := by
  change F1 * Q * F1⁻¹ = _
  rw [Monomial.inv_of_square F1_square]
  exact of_derivable Monomial.X1_ccZ_flip

theorem flip1_D : flip1 D = D⁻¹ * S0 := by
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xl * Two.W2.CS * Two.W2.Xl)
    (v := Two.W2.CS ^ 3 * Two.W2.Su) (by decide +kernel)))
  change F1 * D * F1 = D ^ 3 * S0 at h
  change F1 * D * F1⁻¹ = _
  rw [Monomial.inv_of_square F1_square, h, Monomial.cube_eq_inv Monomial.d_fourth]

theorem double_flip : F1 * F2 * Q * F2 * F1 = Q * C ^ 2 * D ^ 2 * S0 ^ 2 := by
  have h2 : F2 * Q * F2 = Q * D ^ 2 := of_derivable Monomial.X2_ccZ
  have hd : D ^ 2 * D ^ 2 = 1 := by
    rw [← pow_add]
    exact Monomial.d_fourth
  have hi : D⁻¹ ^ 2 = D ^ 2 := by rw [inv_pow, Monomial.inv_of_square hd]
  calc
    F1 * F2 * Q * F2 * F1 = F1 * (Q * D ^ 2) * F1 := by
      rw [← h2]
      group
    _ = flip1 (Q * D ^ 2) := by
      change _ = F1 * (Q * D ^ 2) * F1⁻¹
      rw [Monomial.inv_of_square F1_square]
    _ = (Q * C ^ 2) * (D⁻¹ * S0) ^ 2 := by rw [map_mul, map_pow, flip1_Q, flip1_D]
    _ = Q * C ^ 2 * D ^ 2 * S0 ^ 2 := by
      rw [S0_D.symm.inv_left.mul_pow, hi]
      group

theorem token2_form : u (Cert.token 2) = K * (Q * C ^ 2 * D ^ 2 * S0 ^ 2) * K⁻¹ := by
  have ht : u (Cert.token 2) = F1 * F2 * T * F2 * F1 := rfl
  have hk : Commute (F1 * F2) K := F1_K.mul_left Monomial.f2_K0_commute
  have hk' : Commute (F2 * F1) K := Monomial.f2_K0_commute.mul_left F1_K
  rw [ht, T_eq]
  calc
    F1 * F2 * (K * Q * K⁻¹) * F2 * F1 =
        ((F1 * F2) * K) * Q * (K⁻¹ * (F2 * F1)) := by group
    _ = (K * (F1 * F2)) * Q * ((F2 * F1) * K⁻¹) := by
      rw [hk.eq, hk'.inv_right.symm.eq]
    _ = K * (F1 * F2 * Q * F2 * F1) * K⁻¹ := by group
    _ = _ := by rw [double_flip]

theorem reverse_phases : S0 ^ 2 * D ^ 2 * C ^ 2 * Q = Q * C ^ 2 * D ^ 2 * S0 ^ 2 := by
  have hq := ((S0_Q.pow_left 2).mul_left (D_Q.pow_left 2)).mul_left (C_Q.pow_left 2)
  have hs := ((S0_D.pow_left 2).pow_right 2).mul_right ((S0_C.pow_left 2).pow_right 2)
  have hd := (Monomial.c_d_commute.symm.pow_left 2).pow_right 2
  calc
    S0 ^ 2 * D ^ 2 * C ^ 2 * Q = Q * (S0 ^ 2 * D ^ 2 * C ^ 2) := hq.eq
    _ = Q * ((D ^ 2 * C ^ 2) * S0 ^ 2) := by rw [mul_assoc (S0 ^ 2), hs.eq]
    _ = Q * ((C ^ 2 * D ^ 2) * S0 ^ 2) := by rw [hd.eq]
    _ = _ := by group

theorem atom_token2 : Commute A (u (Cert.token 2)) := by
  have ht := congrArg sw (of_derivable Cert.AtomWhite.comm_white)
  have hS : sw (u (W.S 1)) = S0 := Monomial.swap_conjugates_s1
  change sw (AM * (u (W.K 1) * u (W.S 1) ^ 2 * D ^ 2 * P ^ 2 * R * u (W.I * W.K 1))) =
    sw ((u (W.K 1) * u (W.S 1) ^ 2 * D ^ 2 * P ^ 2 * R * u (W.I * W.K 1)) * AM) at ht
  simp only [map_mul, map_pow, sw_A, sw_K, hS, sw_D, sw_P, sw_R, sw_I, IK] at ht
  have hPS : Commute P S0 :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.S)).symm
  have hPD : Commute P D := Monomial.b_d_commute
  have hPC : Commute P C := Monomial.c_b_commute.symm
  have hFP := ((hPS.pow_right 2).mul_right (hPD.pow_right 2)).mul_right (hPC.pow_right 2)
  have he : K * S0 ^ 2 * D ^ 2 * C ^ 2 * (P * Q) * K⁻¹ = P * u (Cert.token 2) := by
    calc
      K * S0 ^ 2 * D ^ 2 * C ^ 2 * (P * Q) * K⁻¹ =
          K * ((S0 ^ 2 * D ^ 2 * C ^ 2) * P) * Q * K⁻¹ := by group
      _ = K * (P * (S0 ^ 2 * D ^ 2 * C ^ 2)) * Q * K⁻¹ := by rw [hFP.symm.eq]
      _ = (K * P) * (S0 ^ 2 * D ^ 2 * C ^ 2 * Q) * K⁻¹ := by group
      _ = (P * K) * (Q * C ^ 2 * D ^ 2 * S0 ^ 2) * K⁻¹ := by rw [P_K.symm.eq, reverse_phases]
      _ = P * u (Cert.token 2) := by rw [token2_form]; group
  rw [he] at ht
  exact cancel_phase_commute ht

end
end QCert.CliffordCS3.Three.AtomTokens
