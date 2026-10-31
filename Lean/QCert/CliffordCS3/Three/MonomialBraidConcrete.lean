/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The six easy hypotheses of the Toffoli braid

Only the opposite-control commutation and the sign's response to X₂ are
parameters. The former is supplied by the controlled-gate calculation.
-/
import QCert.CliffordCS3.Three.MonomialAffine
import QCert.CliffordCS3.Three.MonomialBraid
import QCert.CliffordCS3.Three.PhaseSymmetry
import QCert.CliffordCS3.Three.PhaseFlip2
import QCert.CliffordCS3.Three.CrossCommutation

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.MonomialBraidConcrete
open QuotientGroup Monomial
noncomputable section

abbrev t : Word Gen := Cert.token 6
abbrev w : Word Gen := swapWord
abbrev z : Word Gen := W.X 2

theorem z_commutes_K (j : Fin 2) : Commute (u z) (u (W.K j.castSucc)) := by
  have hk : Commute (u (W.K 2)) (u (W.K j.castSucc)) := by
    exact of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K j.castSucc 2
      (by fin_cases j <;> decide))).symm
  have hs : Commute (u (W.S 2)) (u (W.K j.castSucc)) := by
    exact of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S j.castSucc 2
      (by fin_cases j <;> decide))).symm
  have hi : Commute (u W.I) (u (W.K j.castSucc)) := by
    exact of_derivable (Derivable.of (Rel.comm_i (Local.K.on j.castSucc)
      (by fin_cases j <;> decide)))
  simpa only [z, W.X, map_mul] using
    (((hk.mul_left hs).mul_left hs).mul_left hk).mul_left hi

theorem z_commutes_d : Commute (u z) dQ := by
  have hk : Commute (u (W.K 2)) dQ :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.K))
  have hs : Commute (u (W.S 2)) dQ :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.S))
  have hi : Commute (u W.I) dQ :=
    of_derivable (Derivable.of (Rel.comm_i .CS₀₁ (by decide)))
  simpa only [z, W.X, map_mul] using
    (((hk.mul_left hs).mul_left hs).mul_left hk).mul_left hi

theorem w_z_commute : Derivable Rel (w * z) (z * w) := by
  apply to_derivable
  have hi : Commute (u z) (u W.I) := by
    have hk : Commute (u (W.K 2)) (u W.I) :=
      of_derivable (Derivable.of (Rel.comm_i .K₂ (by decide))).symm
    have hs : Commute (u (W.S 2)) (u W.I) :=
      of_derivable (Derivable.of (Rel.comm_i .S₂ (by decide))).symm
    simpa only [z, W.X, map_mul] using
      (((hk.mul_left hs).mul_left hs).mul_left hk).mul_left (Commute.refl _)
  have ha : Commute (u z) aQ := by
    simpa only [aQ, W.CX01, W.CX, map_mul] using
      ((((z_commutes_K 1).mul_right z_commutes_d).mul_right z_commutes_d).mul_right
        (z_commutes_K 1)).mul_right hi
  have hx : Commute (u z) xQ := by
    simpa only [xQ, W.CX10, W.CX, map_mul] using
      ((((z_commutes_K 0).mul_right z_commutes_d).mul_right z_commutes_d).mul_right
        (z_commutes_K 0)).mul_right hi
  simpa only [w, swapWord, map_mul] using ((ha.mul_right hx).mul_right ha).symm.eq

theorem tztz
    (hflip : Derivable Rel (z * Cert.ccZ * z) (Cert.ccZ * W.CS01 ^ 2)) :
    Derivable Rel (t * z * t * z) W.CX10 := by
  apply to_derivable
  have hi : (u (W.K 0))⁻¹ = u (W.I * W.K 0) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 0)
  have ht : u t = u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹ := by rw [hi]; rfl
  have hf := of_derivable hflip
  simp only [map_mul, map_pow] at hf
  have hzK : Commute (u z) (u (W.K 0)) := z_commutes_K 0
  have hconj : u z * u t * u z = u t * xQ := by
    rw [ht]
    have hkx : u (W.K 0) * dQ ^ 2 * (u (W.K 0))⁻¹ = xQ := by
      rw [← K0_conjugates_CX10]; group
    calc
      u z * (u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹) * u z =
          (u z * u (W.K 0)) * u Cert.ccZ * ((u (W.K 0))⁻¹ * u z) := by group
      _ = (u (W.K 0) * u z) * u Cert.ccZ * (u z * (u (W.K 0))⁻¹) := by
        rw [hzK.eq, hzK.symm.inv_left.eq]
      _ = u (W.K 0) * (u z * u Cert.ccZ * u z) * (u (W.K 0))⁻¹ := by group
      _ = u (W.K 0) * (u Cert.ccZ * dQ ^ 2) * (u (W.K 0))⁻¹ := by rw [hf]
      _ = (u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹) * xQ := by rw [← hkx]; group
  have hts : u t * u t = 1 := by
    simpa only [map_mul, map_one] using of_derivable (token_square ccZ_square 6)
  simp only [map_mul, mul_assoc]
  rw [← mul_assoc (u z), hconj, ← mul_assoc, hts, one_mul]

theorem six_of_flip_and_cross
    (hflip : Derivable Rel (z * Cert.ccZ * z) (Cert.ccZ * W.CS01 ^ 2))
    (hcross : Derivable Rel (t * w * z * t * z * w) (w * z * t * z * w * t)) :
    Derivable Rel ((t * w) ^ 6) 1 := by
  have ht := token_square ccZ_square 6
  have hw : Derivable Rel (w * w) 1 := Swap01.sq
  have hz : Derivable Rel (z * z) 1 := X_square 2
  have htz := tztz hflip
  have htz4 : Derivable Rel ((t * z) ^ 4) 1 := by
    have h := htz.mul htz
    have hx : Derivable Rel (W.CX10 * W.CX10) 1 := by
      apply to_derivable
      simpa only [map_mul, map_one] using x_square
    apply (Derivable.of_eq (show (t * z) ^ 4 =
      (t * z * t * z) * (t * z * t * z) by simp only [pow_succ, pow_zero, one_mul, mul_assoc])).trans
    exact h.trans hx
  have hxw : Derivable Rel ((W.CX10 * w) ^ 3) 1 := by
    let cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I
    let cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I
    exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := (cu * (cl * cu * cl)) ^ 3) (v := 1) (by decide +kernel))
  have hxorder := (htz.mul_right w).pow 3
  exact MonomialBraid.six_of t w z ht hw hz w_z_commute htz4 (hxorder.trans hxw) hcross

theorem swap_token : Derivable Rel (w * t * w) (ccx 1) := by
  apply to_derivable
  have hs : u w * u w = 1 := by
    simpa only [map_mul, map_one] using of_derivable Swap01.sq
  have hss (v : G) : u w * (u w * v) = v := by rw [← mul_assoc, hs, one_mul]
  have hk1 : u w * u (W.K 1) * u w = u (W.K 0) := by
    simpa only [map_mul] using of_derivable Swap01.conjugate_K
  have hk0 : u w * u (W.K 0) * u w = u (W.K 1) := by
    rw [← hk1]
    simp only [mul_assoc, hss, hs, mul_one]
  have hi : u w * u W.I * u w = u W.I := by
    simpa only [map_mul] using of_derivable Swap01.conjugate_I
  have hq : u w * u Cert.ccZ * u w = u Cert.ccZ := by
    simpa only [map_mul] using of_derivable swap_ccZ
  have ht : t = W.K 0 * Cert.ccZ * (W.I * W.K 0) := rfl
  simp only [map_mul, ht, ccx]
  have hsInv := inv_of_square hs
  calc
    u w * (u (W.K 0) * u Cert.ccZ * (u W.I * u (W.K 0))) * u w =
        (u w * u (W.K 0) * u w) * (u w * u Cert.ccZ * u w) *
          ((u w * u W.I * u w) * (u w * u (W.K 0) * u w)) := by
      have h : u w * (u (W.K 0) * u Cert.ccZ * (u W.I * u (W.K 0))) * (u w)⁻¹ =
          (u w * u (W.K 0) * (u w)⁻¹) * (u w * u Cert.ccZ * (u w)⁻¹) *
            ((u w * u W.I * (u w)⁻¹) * (u w * u (W.K 0) * (u w)⁻¹)) := by group
      simpa only [hsInv] using h
    _ = u (W.K 1) * u Cert.ccZ * (u W.I * u (W.K 1)) := by rw [hk0, hi, hq]

/-- The two black-control Toffoli gates satisfy the braid once opposite
controls are proved disjoint. -/
theorem braid_of_flip_and_cross
    (hflip : Derivable Rel (z * Cert.ccZ * z) (Cert.ccZ * W.CS01 ^ 2))
    (hcross : Derivable Rel (t * w * z * t * z * w) (w * z * t * z * w * t)) :
    Derivable Rel (ccx 0 * ccx 1 * ccx 0) (ccx 1 * ccx 0 * ccx 1) := by
  apply to_derivable
  have hsix : (u t * u w) ^ 6 = 1 := by
    simpa only [map_mul, map_pow, map_one] using of_derivable (six_of_flip_and_cross hflip hcross)
  have hpair : u t * u (ccx 1) = (u t * u w) ^ 2 := by
    have he := of_derivable swap_token
    rw [← he]
    simp only [map_mul, sq, mul_assoc]
  have hcube : (u t * u (ccx 1)) ^ 3 = 1 := by
    rw [hpair, ← pow_mul]; exact hsix
  have ht : u t * u t = 1 := by
    simpa only [map_mul, map_one] using of_derivable (token_square ccZ_square 6)
  have hv : u (ccx 1) * u (ccx 1) = 1 := by
    simpa only [map_mul, map_one] using of_derivable (ccx_square 1 ccZ_square)
  have he : (u t * u (ccx 1) * u t) * (u (ccx 1) * u t * u (ccx 1)) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hcube
  have heq := eq_inv_of_mul_eq_one_left he
  simp only [mul_inv_rev, inv_of_square ht, inv_of_square hv, mul_assoc] at heq
  simpa only [map_mul, mul_assoc] using heq

theorem opposite_word : u (w * z * t * z * w) = CrossCommutation.O := by
  have hwz : Commute (u w) (u z) := of_derivable w_z_commute
  have hwtw : u w * u t * u w = u (ccx 1) := by
    simpa only [map_mul] using of_derivable swap_token
  have hzK : Commute (u z) (u (W.K 1)) := z_commutes_K 1
  have hi : (u (W.K 1))⁻¹ = u (W.I * W.K 1) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 1)
  have hccx : u (ccx 1) = u (W.K 1) * u Cert.ccZ * (u (W.K 1))⁻¹ := by
    rw [hi]; rfl
  have hflip := of_derivable X2_ccZ
  simp only [map_mul, map_pow] at hflip
  calc
    u (w * z * t * z * w) = (u w * u z) * u t * (u z * u w) := by
      simp only [map_mul, mul_assoc]
    _ = (u z * u w) * u t * (u z * u w) := by rw [hwz.eq]
    _ = (u z * u w) * u t * (u w * u z) := by
      exact congrArg (fun v : G => (u z * u w) * u t * v) hwz.symm.eq
    _ = u z * (u w * u t * u w) * u z := by group
    _ = u z * u (ccx 1) * u z := by rw [hwtw]
    _ = (u z * u (W.K 1)) * u Cert.ccZ * ((u (W.K 1))⁻¹ * u z) := by
      rw [hccx]; group
    _ = (u (W.K 1) * u z) * u Cert.ccZ * (u z * (u (W.K 1))⁻¹) := by
      rw [hzK.eq, hzK.symm.inv_left.eq]
    _ = u (W.K 1) * (u z * u Cert.ccZ * u z) * (u (W.K 1))⁻¹ := by group
    _ = CrossCommutation.O := by rw [hflip]; rfl

theorem opposite_commute :
    Derivable Rel (t * w * z * t * z * w) (w * z * t * z * w * t) := by
  apply to_derivable
  have h := CrossCommutation.token_opposite_commute.eq
  rw [← opposite_word] at h
  simpa only [map_mul, mul_assoc] using h

/-- The two black-control Toffoli transpositions satisfy the Coxeter braid. -/
theorem toffoli_braid :
    Derivable Rel (ccx 0 * ccx 1 * ccx 0) (ccx 1 * ccx 0 * ccx 1) :=
  braid_of_flip_and_cross X2_ccZ opposite_commute

theorem toffoli_swap_six : Derivable Rel ((t * w) ^ 6) 1 :=
  six_of_flip_and_cross X2_ccZ opposite_commute

theorem CX01_toffoli_conjugate :
    Derivable Rel (W.CX01 * ccx 0 * W.CX01) (ccx 1 * ccx 0 * ccx 1) := by
  apply to_derivable
  let T : G := u t
  let S : G := u (ccx 1)
  let Z : G := u z
  let V : G := Z * S * Z
  have ht : T * T = 1 := by
    simpa only [map_mul, map_one] using of_derivable (token_square ccZ_square 6)
  have hs : S * S = 1 := by
    simpa only [map_mul, map_one] using of_derivable (ccx_square 1 ccZ_square)
  have hz : Z * Z = 1 := by
    simpa only [map_mul, map_one] using of_derivable (X_square 2)
  have hw : u w * u w = 1 := by
    simpa only [map_mul, map_one] using of_derivable Swap01.sq
  have hwz : Commute (u w) Z := of_derivable w_z_commute
  have hwtw : u w * T * u w = S := by
    simpa only [map_mul] using of_derivable swap_token
  have hwx : u w * xQ * u w = aQ := by
    let cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I
    let cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I
    exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := (cl * cu * cl) * cu * (cl * cu * cl)) (v := cl) (by decide +kernel)))
  have hswapZ : u w * Z * u w = Z := by rw [hwz.eq, mul_assoc, hw, mul_one]
  have hrec : T * Z * T * Z = xQ := by
    simpa only [map_mul] using of_derivable (tztz X2_ccZ)
  have ha : aQ = S * V := by
    rw [← hwx, ← hrec]
    have hwi := inv_of_square hw
    calc
      u w * (T * Z * T * Z) * u w =
          (u w * T * u w) * (u w * Z * u w) *
            (u w * T * u w) * (u w * Z * u w) := by
        have he : u w * (T * Z * T * Z) * (u w)⁻¹ =
            (u w * T * (u w)⁻¹) * (u w * Z * (u w)⁻¹) *
              (u w * T * (u w)⁻¹) * (u w * Z * (u w)⁻¹) := by group
        simpa only [hwi] using he
      _ = S * V := by rw [hwtw, hswapZ]; rfl
  have hv : V * V = 1 := by
    dsimp [V]
    have hzz (v : G) : Z * (Z * v) = v := by rw [← mul_assoc, hz, one_mul]
    simp only [mul_assoc, hzz, ← mul_assoc S S, hs, one_mul, hz]
  have hsv : Commute S V := by
    have hsq : (S * V) * (S * V) = 1 := by rw [← ha]; exact a_square
    have he := (eq_inv_of_mul_eq_one_left hsq)
    simpa only [mul_inv_rev, inv_of_square hs, inv_of_square hv] using he
  have htv : Commute T V := by
    have h := CrossCommutation.token_opposite_commute
    have hvO : V = CrossCommutation.O := by
      have hopen := opposite_word
      have he : u (w * z * t * z * w) = V := by
        simp only [map_mul]
        calc
          u w * Z * T * Z * u w = (u w * Z) * T * (Z * u w) := by group
          _ = (Z * u w) * T * (Z * u w) := by rw [hwz.eq]
          _ = (Z * u w) * T * (u w * Z) :=
            congrArg (fun v : G => (Z * u w) * T * v) hwz.symm.eq
          _ = Z * (u w * T * u w) * Z := by group
          _ = V := by rw [hwtw]
      exact he.symm.trans hopen
    rwa [← hvO] at h
  simp only [map_mul]
  change aQ * T * aQ = S * T * S
  rw [ha]
  calc
    (S * V) * T * (S * V) = S * (V * T) * S * V := by group
    _ = S * (T * V) * S * V := by rw [htv.symm.eq]
    _ = S * T * (V * S) * V := by group
    _ = S * T * (S * V) * V := by rw [hsv.symm.eq]
    _ = S * T * S := by simp only [mul_assoc, hv, mul_one]

end
end QCert.CliffordCS3.Three.MonomialBraidConcrete

