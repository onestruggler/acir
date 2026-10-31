/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The pair phase fixes exchanges outside its support
-/
import QCert.CliffordCS3.Three.PhaseDressed
import QCert.CliffordCS3.Three.Cert.PhaseWhite

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PhaseStabilizers

open QuotientGroup LocalKZ AtomTokens PhaseCases PhaseDressed
noncomputable section

theorem S1_C : Commute S1 C := by
  have hs : sw S0 = S1 :=
    of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Swap01.pair * Two.W2.Su * Swap01.pair) (v := Two.W2.Sl)
      (by decide +kernel)))
  have h := Monomial.s0_b_commute.map sw
  change Commute (sw S0) (sw P) at h
  rwa [hs, sw_P] at h

private theorem cancel_commute {c x y : G} (hc : Commute x c)
    (h : Commute x (c * y)) : Commute x y := by
  apply mul_left_cancel (a := c)
  calc
    c * (x * y) = x * (c * y) := by rw [← mul_assoc, hc.symm.eq, mul_assoc]
    _ = c * y * x := h.eq
    _ = c * (y * x) := by group

theorem phase_token3 : Commute P (u (Cert.token 3)) := by
  have ht := of_derivable Cert.PhaseWhite.conjugate
  simp only [map_mul, map_pow] at ht
  have hi : u W.I * u (W.K 1) = (u (W.K 1))⁻¹ := by
    simpa only [map_mul] using K_inv 1
  rw [hi, Monomial.cube_eq_inv Monomial.b_fourth] at ht
  change Commute (P⁻¹ * S1) (u (W.K 1) * R * (u (W.K 1))⁻¹) at ht
  have hR : u (W.K 1) * R * (u (W.K 1))⁻¹ = C * WhiteSign.U1 := by
    rw [R_eq, ← mul_assoc, WhiteSign.c_K1_commute.symm.eq]
    group
  rw [hR] at ht
  have hc : Commute (P⁻¹ * S1) C :=
    Monomial.c_b_commute.symm.inv_left.mul_left S1_C
  have hh := (cancel_commute hc ht).conj F2
  rw [Monomial.inv_of_square Monomial.f2_square] at hh
  have hf : F2 * P * F2 = P⁻¹ * S1 := Monomial.f2_conjugates_b
  have he : F2 * (P⁻¹ * S1) * F2 = P := by
    rw [← hf]
    have hs (x : G) : F2 * (F2 * x) = x := by
      rw [← mul_assoc, Monomial.f2_square, one_mul]
    simp only [mul_assoc, hs, Monomial.f2_square, mul_one]
  rw [he] at hh
  have hT : F2 * WhiteSign.U1 * F2 = u (Cert.token 3) := by
    rw [WhiteSign.U1, ← K_inv 1]
    rfl
  rwa [hT] at hh

theorem phase_token1 : Commute P (u (Cert.token 1)) := by
  have h3 : u (Cert.token 3) = F2 * (u (W.K 1) * Q * (u (W.K 1))⁻¹) * F2 := by
    rw [← K_inv 1]
    rfl
  have ht := phase_token3.map sw12
  rw [sw12_P, h3] at ht
  simp only [map_mul, map_inv, sw12_F2, sw12_K1, sw12_Q] at ht
  have hh := ht.conj F0
  rw [Monomial.inv_of_square Monomial.flip0_square] at hh
  have hp : F0 * P * F0 = P := by
    simpa only [Monomial.conj0_eq] using Monomial.conj0_b
  rw [hp] at hh
  have he : F0 * (F1 * (K2 * Q * K2⁻¹) * F1) * F0 = u (Cert.token 1) := by
    rw [← K_inv 2]
    rfl
  rwa [he] at hh

theorem phase_token (d : Fin 5) : Commute P (u (Cert.token d.castSucc.castSucc)) := by
  fin_cases d
  · exact Cert.KStabilizers.phase_token0
  · exact phase_token1
  · exact Cert.KStabilizers.phase_token2
  · exact phase_token3
  · exact Cert.KStabilizers.phase_token4

end
end QCert.CliffordCS3.Three.PhaseStabilizers
