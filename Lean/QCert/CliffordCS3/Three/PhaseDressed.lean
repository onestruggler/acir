/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The dressed last transposition in the odd determinant coset

Two pair phases conjugate the last transposition to its coset residual.
Conjugating the ordinary permutation equations then supplies their
dressed versions.
-/
import QCert.CliffordCS3.Three.PhaseCases
import QCert.CliffordCS3.Three.Cert.PhaseConjugation
import QCert.CliffordCS3.Three.Cert.KStabilizers

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhaseDressed

open QuotientGroup LocalKZ AtomTokens PhaseCases
noncomputable section

abbrev U : G := P * T * Q
abbrev S1 : G := u (W.S 1)
abbrev U2 : G := K2 * Q * K2⁻¹

theorem C_dresses : C * T * C⁻¹ = U := by
  have ht := congrArg sw (of_derivable Cert.PhaseConjugation.conjugate)
  simp only [map_mul, map_pow, sw_K, sw_R, sw_I, IK] at ht
  change C * (K * (P * Q) * K⁻¹) * C ^ 3 =
    (K * (P * Q) * K⁻¹) * (P * Q) at ht
  have hc : Commute C P := Monomial.c_b_commute
  have hCP : C ^ 3 = C⁻¹ := by
    have h4 : C ^ 4 = 1 := by
      have h := congrArg sw P_fourth
      simpa only [map_pow, sw_P, map_one] using h
    exact Monomial.cube_eq_inv h4
  have hF : K * (P * Q) * K⁻¹ = P * T := by
    rw [T_eq, ← mul_assoc K P Q, P_K.symm.eq]
    group
  rw [hF, hCP] at ht
  apply mul_left_cancel (a := P)
  calc
    P * (C * T * C⁻¹) = C * (P * T) * C⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, hc.symm.eq]
      group
    _ = (P * T) * (P * Q) := ht
    _ = P * (P * T * Q) := by
      have hp : Commute P T := (of_derivable Monomial.phase_token6_commute).symm
      rw [mul_assoc P T (P * Q), ← mul_assoc T P Q, hp.symm.eq]

theorem sw12_K0 : sw12 K = K := by
  have hk1 : Commute K (u (W.K 1)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 1 (by decide)))
  have hk2 : Commute K K2 :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 2 (by decide)))
  have hi : Commute K (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .K₀ (by decide))).symm
  have hy : Commute K Monomial.yQ := by
    simpa only [Monomial.yQ, W.CX21, W.CX, map_mul] using
      (((hk1.mul_right P_K.symm).mul_right P_K.symm).mul_right hk1).mul_right hi
  have hs : Commute K Monomial.swap12Q :=
    (hy.mul_right Monomial.K0_z_commute).mul_right hy
  change Monomial.swap12Q * K * Monomial.swap12Q⁻¹ = K
  rw [hs.symm.eq]
  group

theorem sw12_T : sw12 T = T := by
  rw [T_eq]
  simp only [map_mul, map_inv, sw12_K0, sw12_Q]

private def pair12 : Word Two.Gen2 :=
  (Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I) *
  (Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I) *
  (Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I)

theorem sw12_P : sw12 P = P := by
  rw [sw12_eq]
  exact of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := pair12 * Two.W2.CS * pair12) (v := Two.W2.CS)
    (by decide +kernel)))

theorem sw12_C : sw12 C = D := by
  rw [sw12_eq]
  change Monomial.swap12Q * Monomial.cQ * Monomial.swap12Q = Monomial.dQ
  rw [← Monomial.swap12_d]
  have hsq := Monomial.swap12_square
  have hs (x : G) : Monomial.swap12Q * (Monomial.swap12Q * x) = x := by
    rw [← mul_assoc, hsq, one_mul]
  simp only [mul_assoc, hs, hsq, mul_one]

theorem D_dresses : D * T * D⁻¹ = U := by
  have h := congrArg sw12 C_dresses
  simpa only [map_mul, map_inv, sw12_C, sw12_T, U, sw12_P, sw12_Q] using h

theorem D_U2 : Commute D U2 := by
  have hk : Commute D K2 :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.K)).symm
  exact (hk.mul_right D_Q).mul_right hk.inv_right

theorem S1_Q : Commute S1 Q := by
  have hs : sw S0 = S1 :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Swap01.pair * Two.W2.Su * Swap01.pair) (v := Two.W2.Sl)
      (by decide +kernel)))
  have ht := S0_Q.map sw
  rwa [hs, sw_Q] at ht

theorem S1_U2 : Commute S1 U2 := by
  have hk : Commute S1 K2 :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 1 2 (by decide)))
  exact (hk.mul_right S1_Q).mul_right hk.inv_right

theorem S0_U2 : Commute S0 U2 := by
  have hk : Commute S0 K2 :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 2 (by decide)))
  exact (hk.mul_right S0_Q).mul_right hk.inv_right

theorem F0_D : F0 * D * F0 = D⁻¹ * S1 := by
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * Two.W2.CS * Two.W2.Xu)
    (v := Two.W2.CS ^ 3 * Two.W2.Sl) (by decide +kernel)))
  change F0 * D * F0 = D ^ 3 * S1 at h
  rwa [Monomial.cube_eq_inv Monomial.d_fourth] at h

theorem token5_form : u (Cert.token 5) = F0 * U2 * F0 := by
  rw [U2, ← K_inv 2]
  rfl

theorem D_token5 : Commute D (u (Cert.token 5)) := by
  have hf : F0⁻¹ = F0 := Monomial.inv_of_square Monomial.flip0_square
  have h : Commute (F0⁻¹ * D * F0) U2 := by
    rw [hf, F0_D]
    exact D_U2.inv_left.mul_left S1_U2
  have ht := Monomial.commute_conjugate h
  rwa [hf, ← token5_form] at ht

theorem D_token1 : Commute D (u (Cert.token 1)) := by
  let f : G := F0 * F1
  have hi : Commute (u W.I) U2 := by
    have hk : Commute (u W.I) K2 :=
      of_derivable (Derivable.of (Rel.comm_i .K₂ (by decide)))
    have hq : Commute (u W.I) Q := by
      have h1 : Commute (u W.I) Monomial.aQ := by
        exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
          (w := Two.W2.I * (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I))
          (v := (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) * Two.W2.I)
          (by decide +kernel)))
      have hb : Commute (u W.I) P :=
        of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide)))
      have hc : Commute (u W.I) C := by
        have hs : Commute (u W.I) S :=
          of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
            (w := Two.W2.I * Swap01.pair) (v := Swap01.pair * Two.W2.I)
            (by decide +kernel)))
        exact (hs.mul_right hb).mul_right hs
      rw [show Q = C⁻¹ * (Monomial.aQ * P * Monomial.aQ) * P⁻¹ from Monomial.u_ccZ]
      exact (hc.inv_right.mul_right ((h1.mul_right hb).mul_right h1)).mul_right hb.inv_right
    exact (hk.mul_right hq).mul_right hk.inv_right
  have hform : f⁻¹ * D * f = u W.I * D * S0 ^ 3 * S1 ^ 3 := by
    have hf0 : F0⁻¹ = F0 := Monomial.inv_of_square Monomial.flip0_square
    have hf1 : F1⁻¹ = F1 := Monomial.inv_of_square F1_square
    simp only [f, mul_inv_rev, hf0, hf1]
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Xu * Two.W2.CS * (Two.W2.Xu * Two.W2.Xl))
      (v := Two.W2.I * Two.W2.CS * Two.W2.Su ^ 3 * Two.W2.Sl ^ 3)
      (by decide +kernel)))
  have h : Commute (f⁻¹ * D * f) U2 := by
    rw [hform]
    exact ((hi.mul_left D_U2).mul_left (S0_U2.pow_left 3)).mul_left (S1_U2.pow_left 3)
  have ht := Monomial.commute_conjugate h
  have he : f * U2 * f⁻¹ = u (Cert.token 1) := by
    simp only [f, mul_inv_rev, Monomial.inv_of_square Monomial.flip0_square,
      Monomial.inv_of_square F1_square, U2]
    rw [← K_inv 2]
    rfl
  rwa [he] at ht

theorem C_token3 : Commute C (u (Cert.token 3)) := by
  have hk : Commute C (u (W.K 1)) := WhiteSign.c_K1_commute
  have hU : Commute C WhiteSign.U1 := (hk.mul_right C_Q).mul_right hk.inv_right
  have hs : Commute S0 (u (W.K 1)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.S Local.K 0 1 (by decide)))
  have hS : Commute S0 WhiteSign.U1 := (hs.mul_right S0_Q).mul_right hs.inv_right
  have hi := Monomial.inv_of_square Monomial.f2_square
  have h : Commute (F2⁻¹ * C * F2) WhiteSign.U1 := by
    rw [hi, Monomial.f2_conjugates_c]
    exact hU.inv_left.mul_left hS
  have ht := Monomial.commute_conjugate h
  rw [hi] at ht
  have he : F2 * WhiteSign.U1 * F2 = u (Cert.token 3) := by
    rw [WhiteSign.U1, ← K_inv 1]
    rfl
  rwa [he] at ht

theorem dressed_disjoint (d : Fin 5) (ht : Commute T (u (Cert.token d.castSucc.castSucc))) :
    Commute U (u (Cert.token d.castSucc.castSucc)) := by
  fin_cases d
  · exact (Cert.KStabilizers.phase_token0.mul_left ht).mul_left sign_token0
  · have h := ht.conj D
    rw [D_dresses] at h
    change Commute U (D * u (Cert.token 1) * D⁻¹) at h
    have he : D * u (Cert.token 1) * D⁻¹ = u (Cert.token 1) := by
      rw [D_token1.eq]; group
    rwa [he] at h
  · exact (Cert.KStabilizers.phase_token2.mul_left ht).mul_left sign_token2
  · have h := ht.conj C
    rw [C_dresses] at h
    change Commute U (C * u (Cert.token 3) * C⁻¹) at h
    have he : C * u (Cert.token 3) * C⁻¹ = u (Cert.token 3) := by
      rw [C_token3.eq]; group
    rwa [he] at h
  · exact (Cert.KStabilizers.phase_token4.mul_left ht).mul_left sign_token4

theorem dressed_braid
    (ht : u (Cert.token 5) * T * u (Cert.token 5) = T * u (Cert.token 5) * T) :
    u (Cert.token 5) * U * u (Cert.token 5) = U * u (Cert.token 5) * U := by
  let f : G →* G := (MulAut.conj D).toMonoidHom
  have he : f (u (Cert.token 5)) = u (Cert.token 5) := by
    change D * u (Cert.token 5) * D⁻¹ = u (Cert.token 5)
    rw [D_token5.eq]
    group
  have hu : f T = U := D_dresses
  have h := congrArg f ht
  simpa only [map_mul, he, hu] using h

end
end QCert.CliffordCS3.Three.PhaseDressed
