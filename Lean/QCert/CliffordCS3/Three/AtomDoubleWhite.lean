/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The residual atom fixes the exchange on two white controls
-/
import QCert.CliffordCS3.Three.AtomControlSymmetry

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.AtomDoubleWhite

open QuotientGroup LocalKZ AtomTokens PhaseCases
noncomputable section

abbrev D : G := Monomial.dQ
abbrev S1 : G := u (W.S 1)
abbrev K1 : G := u (W.K 1)
abbrev V : G := AtomCross.V
abbrev O : G := AtomCross.O
def Ow : G := F0 * O * F0

theorem F0_K1 : Commute F0 K1 := of_derivable (Two.derivable_embed 0
  (Two.derivable_of_check2 (w := Two.W2.Xu * Two.W2.Kl)
    (v := Two.W2.Kl * Two.W2.Xu) (by decide +kernel)))

theorem F0_F2 : Commute F0 F2 := by
  have h : Commute F1 F2 := of_derivable (Two.derivable_embed 1
    (Two.derivable_of_check2 (w := Two.W2.Xu * Two.W2.Xl)
      (v := Two.W2.Xl * Two.W2.Xu) (by decide +kernel)))
  have ht := h.map sw
  simpa only [sw_F1, sw_F2] using ht

theorem D_Ow : Commute D Ow := by
  have t3 : u (Cert.token 3) = F2 * (K1 * Q * K1⁻¹) * F2 := by
    rw [← K_inv 1]
    rfl
  have h := PhaseStabilizers.phase_token3.map (sw.comp (sw12.comp sw))
  rw [t3] at h
  simp only [MonoidHom.comp_apply, map_mul, map_inv, sw_P, sw_F2, sw_K, sw_Q,
    PhaseDressed.sw12_C, sw12_F2, PhaseDressed.sw12_K0, sw12_Q,
    sw_D, sw_F1, sw_K0] at h
  have ht := h.conj F2
  rw [Monomial.inv_of_square Monomial.f2_square] at ht
  have hd : F2 * D * F2 = D := by
    rw [Monomial.f2_d_commute.eq, mul_assoc, Monomial.f2_square, mul_one]
  rw [hd] at ht
  have he : F2 * (F0 * (K1 * Q * K1⁻¹) * F0) * F2 = Ow := by
    have ho : O = u (Cert.token 3) := AtomCross.token3_eq.symm
    rw [Ow, ho]
    rw [t3]
    calc
      F2 * (F0 * (K1 * Q * K1⁻¹) * F0) * F2 =
          (F2 * F0) * (K1 * Q * K1⁻¹) * (F0 * F2) := by group
      _ = (F0 * F2) * (K1 * Q * K1⁻¹) * (F2 * F0) := by
        rw [F0_F2.symm.eq, F0_F2.eq]
      _ = _ := by group
  rwa [he] at ht

theorem Ow_form : Ow = K1 * (Q * D ^ 2 * P ^ 2 * S1 ^ 2) * K1⁻¹ := by
  have hq : Monomial.conj0 Q = Q * P ^ 2 := Monomial.conj0_ccZ
  have hd : Monomial.conj0 D = D⁻¹ * S1 := by
    rw [Monomial.conj0_eq]
    exact PhaseDressed.F0_D
  have hs : D⁻¹ ^ 2 = D ^ 2 := by
    rw [inv_pow]
    exact Monomial.inv_of_square (by simpa only [← pow_add] using Monomial.d_fourth)
  have hz : F0 * (Q * D ^ 2) * F0 = Q * D ^ 2 * P ^ 2 * S1 ^ 2 := by
    rw [← Monomial.conj0_eq]
    simp only [map_mul, map_pow, hq, hd]
    rw [Monomial.s1_d_commute.symm.inv_left.mul_pow, hs]
    have hp : Commute (P ^ 2) (D ^ 2) := (Monomial.b_d_commute.pow_left 2).pow_right 2
    calc
      Q * P ^ 2 * (D ^ 2 * S1 ^ 2) = Q * (P ^ 2 * D ^ 2) * S1 ^ 2 := by group
      _ = Q * (D ^ 2 * P ^ 2) * S1 ^ 2 := by rw [hp.eq]
      _ = _ := by group
  change F0 * (K1 * (Q * D ^ 2) * K1⁻¹) * F0 = _
  calc
    F0 * (K1 * (Q * D ^ 2) * K1⁻¹) * F0 =
        (F0 * K1) * (Q * D ^ 2) * (K1⁻¹ * F0) := by group
    _ = (K1 * F0) * (Q * D ^ 2) * (F0 * K1⁻¹) := by
      rw [F0_K1.eq, F0_K1.inv_right.symm.eq]
    _ = K1 * (F0 * (Q * D ^ 2) * F0) * K1⁻¹ := by group
    _ = _ := by rw [hz]

theorem V_K1 : Commute V K1 := by
  have hk : Commute K K1 :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 1 (by decide)))
  have hv : V = C * K * C * K * C := CrossCommutation.F_V
  rw [hv]
  exact (((WhiteSign.c_K1_commute.mul_left hk).mul_left WhiteSign.c_K1_commute).mul_left hk).mul_left
    WhiteSign.c_K1_commute

theorem V_P : Commute V P := by
  have hv : V = C * K * C * K * C := CrossCommutation.F_V
  rw [hv]
  exact (((Monomial.c_b_commute.mul_left P_K.symm).mul_left Monomial.c_b_commute).mul_left
    P_K.symm).mul_left Monomial.c_b_commute

theorem V_S1 : Commute V S1 := by
  have hk : Commute K S1 :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 0 1 (by decide)))
  have hc := PhaseStabilizers.S1_C.symm
  have hv : V = C * K * C * K * C := CrossCommutation.F_V
  rw [hv]
  exact (((hc.mul_left hk).mul_left hc).mul_left hk).mul_left hc

theorem V_Ow : Commute V Ow := by
  rw [Ow_form]
  exact (V_K1.mul_right ((CrossCommutation.FV_opposite.mul_right (V_P.pow_right 2)).mul_right
    (V_S1.pow_right 2))).mul_right V_K1.inv_right

theorem A_Ow : Commute A Ow := by
  rw [AtomCross.A_factor]
  exact (((D_Ow.inv_left.mul_left V_Ow).mul_left D_Ow.inv_left).mul_left
    V_Ow.inv_left).mul_left (D_Ow.pow_left 2)

theorem atom_token1 : Commute A (u (Cert.token 1)) := by
  have h := A_Ow.map sw12
  rw [AtomControlSymmetry.f12_A] at h
  change Commute A (sw12 (F0 * O * F0)) at h
  have ho : O = u (Cert.token 3) := AtomCross.token3_eq.symm
  rw [ho, AtomControlSymmetry.f12_doublewhite] at h
  exact h

end
end QCert.CliffordCS3.Three.AtomDoubleWhite
