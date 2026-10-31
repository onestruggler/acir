/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symmetry of the controlled sign under the second adjacent swap
-/
import QCert.CliffordCS3.Three.MonomialAffine

namespace QCert.CliffordCS3.Three.Monomial

open QuotientGroup
noncomputable section

def swap12Word : Word Gen := W.CX21 * W.CX12 * W.CX21
abbrev swap12Q : G := u swap12Word

private def cu12 : Word Two.Gen2 :=
  Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I
private def cl12 : Word Two.Gen2 :=
  Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I

theorem cnot_braid12 : yQ * zQ * yQ = zQ * yQ * zQ := by
  have ht := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := cu12 * cl12 * cu12) (v := cl12 * cu12 * cl12) (by decide +kernel)))
  simpa [yQ, zQ, cu12, cl12, W.CX21, W.CX12, W.CX, Two.embW, Two.emb] using ht

theorem swap12_square : swap12Q * swap12Q = 1 := by
  change (yQ * zQ * yQ) * (yQ * zQ * yQ) = 1
  have hyy (r : G) : yQ * (yQ * r) = r := by rw [← mul_assoc, y_square, one_mul]
  have hzz (r : G) : zQ * (zQ * r) = r := by rw [← mul_assoc, z_square, one_mul]
  simp only [mul_assoc, hyy, hzz, y_square]

theorem swap12_d : swap12Q * dQ * swap12Q = cQ := by
  have hswap : swap12Q = zQ * yQ * zQ := by
    simpa only [swap12Q, swap12Word, map_mul] using cnot_braid12
  rw [hswap, c_as_alternate_conjugate]
  have hzdz : zQ * dQ * zQ = dQ := by
    rw [d_z_commute.symm.eq, mul_assoc, z_square, mul_one]
  calc
    (zQ * yQ * zQ) * dQ * (zQ * yQ * zQ) =
        zQ * yQ * (zQ * dQ * zQ) * yQ * zQ := by group
    _ = _ := by rw [hzdz]; group

theorem d_conjugate12_commute : Commute dQ (yQ * dQ * yQ) := by
  have hs : Commute (u (W.S 0)) bQ :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.S))
  exact commute_phase_conjugate y_square a_square b_d_commute.symm hs
    a_conjugates_d c14.symm

theorem c_conjugate12_commute : Commute cQ (yQ * dQ * yQ) := by
  have hcy : Commute cQ yQ := by
    have h := commute_third_phase_cnot y_square z_square cnot_braid12 d_z_commute
    simpa only [c_as_alternate_conjugate, mul_assoc] using h
  exact (hcy.mul_right c_d_commute).mul_right hcy

theorem swap12_conjugates_y : swap12Q * yQ * swap12Q = zQ := by
  have hyy (r : G) : yQ * (yQ * r) = r := by rw [← mul_assoc, y_square, one_mul]
  have hzz (r : G) : zQ * (zQ * r) = r := by rw [← mul_assoc, z_square, one_mul]
  change (yQ * zQ * yQ) * yQ * (yQ * zQ * yQ) = zQ
  calc
    (yQ * zQ * yQ) * yQ * (yQ * zQ * yQ) = yQ * zQ * yQ * zQ * yQ := by
      simp only [mul_assoc, hyy]
    _ = zQ * yQ * zQ * zQ * yQ := by rw [cnot_braid12]
    _ = zQ := by simp only [mul_assoc, hzz, y_square, mul_one]

theorem swap12_conjugates_conjugate :
    swap12Q * (yQ * dQ * yQ) * swap12Q = yQ * dQ * yQ := by
  have hs := inv_of_square swap12_square
  calc
    swap12Q * (yQ * dQ * yQ) * swap12Q =
        (swap12Q * yQ * swap12Q) * (swap12Q * dQ * swap12Q) *
          (swap12Q * yQ * swap12Q) := by
      have ht : swap12Q * (yQ * dQ * yQ) * swap12Q⁻¹ =
          (swap12Q * yQ * swap12Q⁻¹) * (swap12Q * dQ * swap12Q⁻¹) *
            (swap12Q * yQ * swap12Q⁻¹) := by group
      simpa only [hs] using ht
    _ = zQ * cQ * zQ := by rw [swap12_conjugates_y, swap12_d]
    _ = yQ * dQ * yQ := by
      rw [c_as_alternate_conjugate]
      have hzz (r : G) : zQ * (zQ * r) = r := by rw [← mul_assoc, z_square, one_mul]
      simp only [mul_assoc, hzz, z_square, mul_one]

theorem swap12_ccZ :
    Derivable Rel (swap12Word * Cert.ccZ * swap12Word) Cert.ccZ := by
  apply to_derivable
  simp only [map_mul, u_ccZ_alternate]
  have hs := inv_of_square swap12_square
  have hsc : swap12Q * cQ * swap12Q = dQ := by
    rw [← swap12_d]
    have hss (r : G) : swap12Q * (swap12Q * r) = r := by
      rw [← mul_assoc, swap12_square, one_mul]
    simp only [mul_assoc, hss, swap12_square, mul_one]
  calc
    swap12Q * (cQ⁻¹ * (yQ * dQ * yQ) * dQ⁻¹) * swap12Q =
        (swap12Q * cQ * swap12Q)⁻¹ * (swap12Q * (yQ * dQ * yQ) * swap12Q) *
          (swap12Q * dQ * swap12Q)⁻¹ := by
      have ht : swap12Q * (cQ⁻¹ * (yQ * dQ * yQ) * dQ⁻¹) * swap12Q⁻¹ =
          (swap12Q * cQ * swap12Q⁻¹)⁻¹ * (swap12Q * (yQ * dQ * yQ) * swap12Q⁻¹) *
            (swap12Q * dQ * swap12Q⁻¹)⁻¹ := by group
      simpa only [hs] using ht
    _ = dQ⁻¹ * (yQ * dQ * yQ) * cQ⁻¹ := by
      rw [hsc, swap12_conjugates_conjugate, swap12_d]
    _ = cQ⁻¹ * (yQ * dQ * yQ) * dQ⁻¹ := by
      have hd := d_conjugate12_commute.inv_left
      have hc := c_conjugate12_commute.inv_left
      rw [hd.eq, mul_assoc, c_d_commute.inv_inv.symm.eq, ← mul_assoc, hc.symm.eq]

end
end QCert.CliffordCS3.Three.Monomial
