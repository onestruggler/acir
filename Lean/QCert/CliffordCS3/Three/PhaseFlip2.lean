/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Flipping the last control of the three-qubit sign

The controlled sign changes by CZ₀₁ when its last input bit is negated.
The proof uses the diagonal calculus and checked two-qubit equations.
-/
import QCert.CliffordCS3.Three.MonomialAffine
import QCert.CliffordCS3.Three.PhaseSymmetry

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.Monomial

open QuotientGroup
noncomputable section

abbrev f2Q : G := u (W.X 2)
abbrev s0Q : G := u (W.S 0)
abbrev s1Q : G := u (W.S 1)

private theorem commute_conj_middle (x y z : G) (h : Commute x y) :
    x * (y * z * y) * x = y * (x * z * x) * y := by
  calc
    x * (y * z * y) * x = (x * y) * z * (y * x) := by group
    _ = (y * x) * z * (y * x) := congrArg (fun t => t * z * (y * x)) h.eq
    _ = (y * x) * z * (x * y) := congrArg (fun t => (y * x) * z * t) h.symm.eq
    _ = y * (x * z * x) * y := by group

theorem f2_square : f2Q * f2Q = 1 := by
  simpa only [map_mul, map_one] using of_derivable (X_square 2)

theorem f2_K1_commute : Commute f2Q (u (W.K 1)) :=
  of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Xl * Two.W2.Ku) (v := Two.W2.Ku * Two.W2.Xl)
    (by decide +kernel)))

theorem f2_I_commute : Commute f2Q (u W.I) :=
  of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Xl * Two.W2.I) (v := Two.W2.I * Two.W2.Xl)
    (by decide +kernel)))

theorem f2_K0_commute : Commute f2Q (u (W.K 0)) := by
  have hk : Commute (u (W.K 0)) (u (W.K 2)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.K 0 2 (by decide)))
  have hs : Commute (u (W.K 0)) (u (W.S 2)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 0 2 (by decide)))
  have hi : Commute (u (W.K 0)) (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .K₀ (by decide))).symm
  simpa only [f2Q, W.X, map_mul] using
    ((((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi).symm

theorem f2_d_commute : Commute f2Q dQ := by
  have hk : Commute dQ (u (W.K 2)) :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.K)).symm
  have hs : Commute dQ (u (W.S 2)) :=
    of_derivable (Derivable.of (Rel.comm_2_01 Local.S)).symm
  have hi : Commute dQ (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .CS₀₁ (by decide))).symm
  simpa only [f2Q, W.X, map_mul] using
    ((((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi).symm

theorem f2_a_commute : Commute f2Q aQ := by
  simpa only [aQ, W.CX01, W.CX, map_mul] using
    (((f2_K1_commute.mul_right f2_d_commute).mul_right f2_d_commute).mul_right
      f2_K1_commute).mul_right f2_I_commute

theorem f2_x_commute : Commute f2Q xQ := by
  simpa only [xQ, W.CX10, W.CX, map_mul] using
    (((f2_K0_commute.mul_right f2_d_commute).mul_right f2_d_commute).mul_right
      f2_K0_commute).mul_right f2_I_commute

theorem f2_swap_commute : Commute f2Q swapQ := by
  simpa only [swapQ, swapWord, map_mul] using
    (f2_a_commute.mul_right f2_x_commute).mul_right f2_a_commute

theorem f2_conjugates_b : f2Q * bQ * f2Q = bQ⁻¹ * s1Q := by
  have h := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Xl * Two.W2.CS * Two.W2.Xl)
    (v := Two.W2.CS ^ 3 * Two.W2.Su) (by decide +kernel)))
  change f2Q * bQ * f2Q = bQ ^ 3 * s1Q at h
  rwa [cube_eq_inv b_fourth] at h

theorem swap_conjugates_s1 : swapQ * s1Q * swapQ = s0Q := by
  exact of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Swap01.pair * Two.W2.Sl * Swap01.pair) (v := Two.W2.Su)
    (by decide +kernel)))

theorem f2_conjugates_c : f2Q * cQ * f2Q = cQ⁻¹ * s0Q := by
  have hs := inv_of_square swap_square
  calc
    f2Q * cQ * f2Q = swapQ * (f2Q * bQ * f2Q) * swapQ := by
      change f2Q * (swapQ * bQ * swapQ) * f2Q = _
      exact commute_conj_middle f2Q swapQ bQ f2_swap_commute
    _ = swapQ * (bQ⁻¹ * s1Q) * swapQ := by rw [f2_conjugates_b]
    _ = (swapQ * bQ * swapQ)⁻¹ * (swapQ * s1Q * swapQ) := by
      have h : swapQ * (bQ⁻¹ * s1Q) * swapQ⁻¹ =
          (swapQ * bQ * swapQ⁻¹)⁻¹ * (swapQ * s1Q * swapQ⁻¹) := by group
      simpa only [hs] using h
    _ = cQ⁻¹ * s0Q := by rw [swap_conjugates_s1]; rfl

theorem a_conjugates_s1 : aQ * s1Q * aQ = s0Q * s1Q * dQ ^ 2 := by
  let cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := cl * Two.W2.Sl * cl)
    (v := Two.W2.Su * Two.W2.Sl * Two.W2.CS ^ 2) (by decide +kernel)))
  simpa [aQ, dQ, s0Q, s1Q, cl, W.CX01, W.CX, Two.embW, Two.emb] using h

theorem s0_a_commute : Commute s0Q aQ := by
  let cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Su * cl) (v := cl * Two.W2.Su) (by decide +kernel)))
  simpa [aQ, s0Q, cl, W.CX01, W.CX, Two.embW, Two.emb] using h

theorem s0_b_commute : Commute s0Q bQ :=
  of_derivable (Derivable.of (Rel.comm_0_12 Local.S))

theorem s0_c_commute : Commute s0Q cQ := by
  have hs : Commute s1Q bQ := of_derivable (Derivable.of (Rel.c6 1))
  have h := hs.conj swapQ
  rw [inv_of_square swap_square, swap_conjugates_s1] at h
  exact h

theorem s0_D_commute : Commute s0Q (aQ * bQ * aQ) :=
  (s0_a_commute.mul_right s0_b_commute).mul_right s0_a_commute

theorem s1_d_commute : Commute s1Q dQ :=
  of_derivable (Derivable.of (Rel.c7 0))

theorem X2_ccZ :
    Derivable Rel (W.X 2 * Cert.ccZ * W.X 2) (Cert.ccZ * W.CS01 ^ 2) := by
  apply to_derivable
  simp only [map_mul, map_pow, u_ccZ]
  have hf := inv_of_square f2_square
  have ha := inv_of_square a_square
  have hD : f2Q * (aQ * bQ * aQ) * f2Q = aQ * (bQ⁻¹ * s1Q) * aQ := by
    calc
      f2Q * (aQ * bQ * aQ) * f2Q = aQ * (f2Q * bQ * f2Q) * aQ := by
        exact commute_conj_middle f2Q aQ bQ f2_a_commute
      _ = _ := by rw [f2_conjugates_b]
  have hm : aQ * (bQ⁻¹ * s1Q) * aQ =
      (aQ * bQ * aQ)⁻¹ * (s0Q * s1Q * dQ ^ 2) := by
    have hh : aQ * (bQ⁻¹ * s1Q) * aQ =
        (aQ * bQ * aQ⁻¹)⁻¹ * (aQ * s1Q * aQ) := by group
    simpa only [ha, a_conjugates_s1] using hh
  have hs0 := (s0_c_commute.mul_right s0_D_commute.inv_right).inv_left
  have hs1 := s1_d_commute.pow_right 2
  have hc := (c_conjugate_commute.inv_right.mul_right c_b_commute)
  have hd := b_d_commute.symm.pow_left 2
  have hb := b_conjugate_commute.symm.inv_left
  have hq := of_derivable ccZ_square
  simp only [map_mul, map_one] at hq
  have hqi := inv_of_square hq
  calc
    f2Q * (cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹) * f2Q =
        (f2Q * cQ * f2Q)⁻¹ * (f2Q * (aQ * bQ * aQ) * f2Q) *
          (f2Q * bQ * f2Q)⁻¹ := by
      have hh : f2Q * (cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹) * f2Q⁻¹ =
          (f2Q * cQ * f2Q⁻¹)⁻¹ * (f2Q * (aQ * bQ * aQ) * f2Q⁻¹) *
            (f2Q * bQ * f2Q⁻¹)⁻¹ := by group
      simpa only [hf] using hh
    _ = (cQ⁻¹ * s0Q)⁻¹ * ((aQ * bQ * aQ)⁻¹ * (s0Q * s1Q * dQ ^ 2)) *
          (bQ⁻¹ * s1Q)⁻¹ := by rw [f2_conjugates_c, hD, hm, f2_conjugates_b]
    _ = (s0Q⁻¹ * (cQ * (aQ * bQ * aQ)⁻¹) * s0Q) *
          (s1Q * dQ ^ 2 * s1Q⁻¹) * bQ := by group
    _ = cQ * (aQ * bQ * aQ)⁻¹ * dQ ^ 2 * bQ := by
      rw [hs0.eq, hs1.eq]
      group
    _ = cQ * ((aQ * bQ * aQ)⁻¹ * bQ) * dQ ^ 2 := by
      rw [mul_assoc (cQ * (aQ * bQ * aQ)⁻¹), hd.eq]
      group
    _ = bQ * (aQ * bQ * aQ)⁻¹ * cQ * dQ ^ 2 := by
      rw [hc.eq, hb.eq]
    _ = (u Cert.ccZ)⁻¹ * dQ ^ 2 := by rw [u_ccZ]; group
    _ = u Cert.ccZ * dQ ^ 2 := by rw [hqi]
    _ = _ := by rw [u_ccZ]

end
end QCert.CliffordCS3.Three.Monomial
