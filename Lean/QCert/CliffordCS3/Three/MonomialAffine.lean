/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Affine transport of the controlled sign
-/
import QCert.CliffordCS3.Three.Monomial
import QCert.CliffordCS3.Three.Conjugation

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.Monomial
open QuotientGroup
noncomputable section

theorem swap_conjugates_d : swapQ * dQ * swapQ = dQ := by
  have h := of_derivable Swap01.conjugate_CS
  simpa only [map_mul] using h

theorem c_d_commute : Commute cQ dQ := by
  have h := b_d_commute.conj swapQ
  rw [inv_of_square swap_square, swap_conjugates_d] at h
  exact h

theorem a_conjugates_d : aQ * dQ * aQ = dQ⁻¹ * u (W.S 0) := by
  let cn : Word Two.Gen2 :=
    Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := cn * Two.W2.CS * cn)
    (v := Two.W2.CS ^ 3 * Two.W2.Su) (by decide +kernel)))
  have h' : aQ * dQ * aQ = dQ ^ 3 * u (W.S 0) := by
    simpa [aQ, dQ, cn, W.CX01, W.CX, Two.embW, Two.emb] using h
  rwa [cube_eq_inv d_fourth] at h'

theorem d_conjugate_commute : Commute dQ (aQ * bQ * aQ) := by
  have hs : Commute (u (W.S 0)) bQ := by
    exact of_derivable (Derivable.of (Rel.comm_0_12 Local.S))
  have hd : Commute (aQ⁻¹ * dQ * aQ) bQ := by
    rw [inv_of_square a_square, a_conjugates_d]
    exact b_d_commute.symm.inv_left.mul_left hs
  have h := commute_conjugate hd
  simpa only [inv_of_square a_square] using h

theorem CS01_ccZ_commute :
    Derivable Rel (W.CS01 * Cert.ccZ) (Cert.ccZ * W.CS01) := by
  apply to_derivable
  simp only [map_mul, u_ccZ]
  exact ((c_d_commute.symm.inv_right).mul_right d_conjugate_commute).mul_right
    b_d_commute.symm.inv_right

theorem K0_conjugates_CX10 :
    (u (W.K 0))⁻¹ * xQ * u (W.K 0) = dQ ^ 2 := by
  have hi : (u (W.K 0))⁻¹ = u (W.I * W.K 0) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 0)
  rw [hi]
  let cn : Word Two.Gen2 :=
    Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := (Two.W2.I * Two.W2.Ku) * cn * Two.W2.Ku)
    (v := Two.W2.CS ^ 2) (by decide +kernel)))
  simpa [xQ, dQ, cn, W.CX10, W.CX, Two.embW, Two.emb] using h

theorem token6_CX10_commute :
    Derivable Rel (Cert.token 6 * W.CX10) (W.CX10 * Cert.token 6) := by
  apply to_derivable
  have hQ : Commute (u Cert.ccZ) dQ := (of_derivable CS01_ccZ_commute).symm
  have h : Commute ((u (W.K 0))⁻¹ * xQ * u (W.K 0)) (u Cert.ccZ) := by
    rw [K0_conjugates_CX10]
    exact (hQ.symm.pow_left 2)
  have hh := commute_conjugate h
  have hi : (u (W.K 0))⁻¹ = u (W.I * W.K 0) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 0)
  rw [hi] at hh
  simpa only [← map_mul] using hh.symm.eq

abbrev zQ : G := u W.CX12

theorem z_square : zQ * zQ = 1 := by
  let cn : Word Two.Gen2 :=
    Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I
  have h := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := cn * cn) (v := 1) (by decide +kernel)))
  simpa [zQ, cn, W.CX12, W.CX, Two.embW, Two.emb] using h

theorem d_z_commute : Commute dQ zQ := by
  have hk : Commute dQ (u (W.K 2)) := by
    exact of_derivable (Derivable.of (Rel.comm_2_01 Local.K)).symm
  have hi : Commute dQ (u W.I) := by
    exact of_derivable (Derivable.of (Rel.comm_i .CS₀₁ (by decide))).symm
  simpa only [zQ, W.CX12, W.CX, map_mul] using
    (((hk.mul_right b_d_commute.symm).mul_right b_d_commute.symm).mul_right hk).mul_right hi

theorem u_ccZ_alternate : u Cert.ccZ = cQ⁻¹ * (yQ * dQ * yQ) * dQ⁻¹ := by
  rw [u_ccZ]
  have h := congrArg (fun x : G => x⁻¹) c14
  simp only [mul_inv_rev, inv_inv, inv_of_square a_square, inv_of_square y_square] at h
  have hh : (aQ * bQ * aQ) * bQ⁻¹ = (yQ * dQ * yQ) * dQ⁻¹ := by
    simpa only [mul_assoc] using h
  simpa only [mul_assoc] using congrArg (fun x : G => cQ⁻¹ * x) hh

theorem c_as_alternate_conjugate : cQ = zQ * (yQ * dQ * yQ) * zQ := by
  have h := of_derivable (Derivable.of Rel.c13)
  simpa only [map_mul, c_as_conjugate, mul_assoc] using h

theorem CX12_conjugates_ccZ :
    Derivable Rel (W.CX12 * Cert.ccZ * W.CX12) (Cert.ccZ * W.CS01 ^ 2) := by
  apply to_derivable
  have hs : u Cert.ccZ * u Cert.ccZ = 1 := by
    simpa only [map_mul, map_one] using of_derivable ccZ_square
  have hp : Commute (u Cert.ccZ) dQ := (of_derivable CS01_ccZ_commute).symm
  simpa only [map_mul, map_pow] using conjugate_triple_phase z_square d_z_commute.symm
    c_as_alternate_conjugate u_ccZ_alternate hs hp d_fourth

theorem CX10_conjugates_ccZ :
    Derivable Rel (W.CX10 * Cert.ccZ * W.CX10) (Cert.ccZ * W.CS12 ^ 2) := by
  apply to_derivable
  have hs : u Cert.ccZ * u Cert.ccZ = 1 := by
    simpa only [map_mul, map_one] using of_derivable ccZ_square
  have hp : Commute (u Cert.ccZ) bQ := (of_derivable phase_ccZ_commute).symm
  simpa only [map_mul, map_pow, mul_assoc] using conjugate_triple_phase x_square b_x_commute.symm
    c_as_conjugate u_ccZ hs hp b_fourth

theorem K0_z_commute : Commute (u (W.K 0)) zQ := by
  have hk : Commute (u (W.K 0)) (u (W.K 2)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 2 (by decide)))
  have hb : Commute (u (W.K 0)) bQ :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.K))
  have hi : Commute (u (W.K 0)) (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .K₀ (by decide))).symm
  simpa only [zQ, W.CX12, W.CX, map_mul] using
    (((hk.mul_right hb).mul_right hb).mul_right hk).mul_right hi

theorem CX12_token6 :
    Derivable Rel (W.CX12 * Cert.token 6) (Cert.token 6 * W.CX10 * W.CX12) := by
  apply to_derivable
  have hi : (u (W.K 0))⁻¹ = u (W.I * W.K 0) := by
    apply (eq_inv_of_mul_eq_one_left ?_).symm
    simpa only [map_mul, map_one] using of_derivable (K_inverse' 0)
  have ht : u (Cert.token 6) = u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹ := by
    rw [hi]; rfl
  have hzx := of_derivable CX12_conjugates_ccZ
  simp only [map_mul, map_pow] at hzx
  have hkx : u (W.K 0) * dQ ^ 2 * (u (W.K 0))⁻¹ = xQ := by
    rw [← K0_conjugates_CX10]; group
  have hzt : zQ * u (Cert.token 6) * zQ = u (Cert.token 6) * xQ := by
    rw [ht, ← hkx]
    calc
      zQ * (u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹) * zQ =
          (zQ * u (W.K 0)) * u Cert.ccZ * ((u (W.K 0))⁻¹ * zQ) := by group
      _ = (u (W.K 0) * zQ) * u Cert.ccZ * (zQ * (u (W.K 0))⁻¹) := by
        rw [K0_z_commute.symm.eq, K0_z_commute.inv_left.eq]
      _ = u (W.K 0) * (zQ * u Cert.ccZ * zQ) * (u (W.K 0))⁻¹ := by group
      _ = u (W.K 0) * (u Cert.ccZ * dQ ^ 2) * (u (W.K 0))⁻¹ := by rw [hzx]
      _ = (u (W.K 0) * u Cert.ccZ * (u (W.K 0))⁻¹) *
          (u (W.K 0) * dQ ^ 2 * (u (W.K 0))⁻¹) := by group
  have h := congrArg (fun v : G => v * zQ) hzt
  simpa only [map_mul, mul_assoc, z_square, mul_one] using h

end
end QCert.CliffordCS3.Three.Monomial

