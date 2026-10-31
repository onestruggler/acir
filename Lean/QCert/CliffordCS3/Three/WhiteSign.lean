/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The sign commutes with an exchange on a white-control branch
-/
import QCert.CliffordCS3.Three.LocalKZ
import QCert.CliffordCS3.Three.PhaseFlip2
import QCert.CliffordCS3.Three.Cert.SignNegative

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.WhiteSign

open QuotientGroup Monomial
noncomputable section

abbrev Q : G := u Cert.ccZ
abbrev K1 : G := u (W.K 1)
abbrev U1 : G := K1 * Q * K1⁻¹
abbrev R : G := LocalKZ.R

theorem c_K1_commute : Commute cQ K1 := by
  have h : Commute bQ (u (W.K 0)) :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hswap : swapQ * u (W.K 0) * swapQ = K1 :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Swap01.pair * Two.W2.Ku * Swap01.pair) (v := Two.W2.Kl)
      (by decide +kernel)))
  have hh := h.conj swapQ
  rw [inv_of_square swap_square, hswap] at hh
  exact hh

theorem c_Q_commute : Commute cQ Q := by
  change Commute cQ (u Cert.ccZ)
  rw [u_ccZ]
  exact (((Commute.refl cQ).inv_right).mul_right c_conjugate_commute).mul_right
    c_b_commute.inv_right

private theorem product_common (c v w : G) (h : Commute c v) :
    (c * v) * (c * w) = (c * c) * (v * w) := by
  calc
    (c * v) * (c * w) = c * (v * c) * w := by group
    _ = c * (c * v) * w := by rw [h.symm.eq]
    _ = (c * c) * (v * w) := by group

theorem phase_sign_commute_exchange : Commute (Q * dQ ^ 2) U1 := by
  have h := of_derivable Cert.SignNegative.sign_negB
  have hi : u W.I * K1 = K1⁻¹ := by simpa only [map_mul] using LocalKZ.K_inv 1
  simp only [map_mul, map_pow] at h
  rw [hi] at h
  change (dQ ^ 2 * R) * (K1 * R * K1⁻¹) =
    (K1 * R * K1⁻¹) * dQ ^ 2 * R at h
  have hdq : Commute dQ Q := of_derivable CS01_ccZ_commute
  have hr : R = cQ * Q := LocalKZ.R_eq
  have hL : dQ ^ 2 * R = cQ * (Q * dQ ^ 2) := by
    rw [hr]
    rw [← mul_assoc, (c_d_commute.pow_right 2).symm.eq, mul_assoc,
      (hdq.pow_left 2).eq]
  have hR : K1 * R * K1⁻¹ = cQ * U1 := by
    rw [hr]
    change K1 * (cQ * Q) * K1⁻¹ = cQ * (K1 * Q * K1⁻¹)
    rw [← mul_assoc K1 cQ Q, c_K1_commute.symm.eq]
    group
  rw [mul_assoc (K1 * R * K1⁻¹) (dQ ^ 2) R, hL, hR] at h
  have hcL : Commute cQ (Q * dQ ^ 2) := c_Q_commute.mul_right (c_d_commute.pow_right 2)
  have hcR : Commute cQ U1 :=
    (c_K1_commute.mul_right c_Q_commute).mul_right c_K1_commute.inv_right
  rw [product_common _ _ _ hcL, product_common _ _ _ hcR] at h
  exact mul_left_cancel h

theorem Q_commute_white_exchange : Commute Q (f2Q * U1 * f2Q) := by
  have h := phase_sign_commute_exchange.conj f2Q
  rw [inv_of_square f2_square] at h
  have hf : f2Q * Q * f2Q = Q * dQ ^ 2 := by
    simpa only [map_mul, map_pow] using of_derivable X2_ccZ
  have he : f2Q * (Q * dQ ^ 2) * f2Q = Q := by
    rw [← hf]
    have hff (z : G) : f2Q * (f2Q * z) = z := by rw [← mul_assoc, f2_square, one_mul]
    simp only [mul_assoc, hff, f2_square, mul_one]
  rwa [he] at h

theorem sign_white_toffoli :
    Derivable Rel (Cert.ccZ * (W.X 2 * ccx 1 * W.X 2))
      ((W.X 2 * ccx 1 * W.X 2) * Cert.ccZ) := by
  apply to_derivable
  have he : u (ccx 1) = U1 := by
    change u (W.K 1 * Cert.ccZ * (W.I * W.K 1)) = _
    rw [map_mul, LocalKZ.K_inv, map_mul]
  simpa only [map_mul, he] using Q_commute_white_exchange.eq

end
end QCert.CliffordCS3.Three.WhiteSign
