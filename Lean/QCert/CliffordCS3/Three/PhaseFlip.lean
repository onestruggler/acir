/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Flipping the first control of the three-qubit sign

Conjugating CCZ by X₀ and multiplying by CCZ gives CZ₁₂. The proof
uses the phase expression from C12–C15 and identities on adjacent pairs.
-/
import QCert.CliffordCS3.Three.MonomialAffine
import QCert.CliffordCS3.Three.PhaseSymmetry

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.Monomial

open QuotientGroup
noncomputable section

abbrev flip0 : G := u (W.X 0)
abbrev flip1 : G := u (W.X 1)

def conj0 : G →* G where
  toFun g := flip0 * g * flip0⁻¹
  map_one' := by group
  map_mul' g h := by group

theorem flip0_square : flip0 * flip0 = 1 := by
  simpa only [map_mul, map_one] using of_derivable (X_square 0)

theorem conj0_eq (g : G) : conj0 g = flip0 * g * flip0 := by
  change flip0 * g * flip0⁻¹ = _
  rw [inv_of_square flip0_square]

private def sw : Word Two.Gen2 :=
  (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I) *
  (Two.W2.Ku * Two.W2.CS ^ 2 * Two.W2.Ku * Two.W2.I) *
  (Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I)

private def cn : Word Two.Gen2 :=
  Two.W2.Kl * Two.W2.CS ^ 2 * Two.W2.Kl * Two.W2.I

theorem flip0_swap : flip0 * swapQ = swapQ * flip1 := by
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * sw) (v := sw * Two.W2.Xl) (by decide +kernel)))
  simpa [flip0, flip1, swapQ, swapWord, sw, W.X, W.CX01, W.CX10, W.CX,
    Two.W2.Xu, Two.W2.Xl, Two.embW, Two.emb, pow_two] using ht

theorem flip1_conjugates_b : flip1 * bQ * flip1 = bQ⁻¹ * sQ := by
  have ht := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := Two.W2.Xu * Two.W2.CS * Two.W2.Xu)
    (v := Two.W2.CS ^ 3 * Two.W2.Sl) (by decide +kernel)))
  have h' : flip1 * bQ * flip1 = bQ ^ 3 * sQ := by
    simpa [flip1, bQ, sQ, W.X, Two.W2.Xu, Two.embW, Two.emb] using ht
  rwa [cube_eq_inv b_fourth] at h'

theorem flip1_a_commute : Commute flip1 aQ := by
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xl * cn) (v := cn * Two.W2.Xl) (by decide +kernel)))
  simpa [flip1, aQ, cn, W.X, W.CX01, W.CX, Two.W2.Xl,
    Two.embW, Two.emb, pow_two] using ht

theorem conj0_a : conj0 aQ = flip1 * aQ := by
  rw [conj0_eq]
  have ht := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := Two.W2.Xu * cn * Two.W2.Xu) (v := Two.W2.Xl * cn)
    (by decide +kernel)))
  simpa [flip0, flip1, aQ, cn, W.X, W.CX01, W.CX,
    Two.W2.Xl, Two.W2.Xu, Two.embW, Two.emb, pow_two] using ht

theorem s_a_commute : Commute sQ aQ := by
  have hk : Commute sQ (u (W.K 1)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 1 2 (by decide))).symm
  have hi : Commute sQ (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .S₂ (by decide))).symm
  simpa only [aQ, W.CX01, W.CX, map_mul] using
    (((hk.mul_right s_d_commute).mul_right s_d_commute).mul_right hk).mul_right hi

theorem s_x_commute : Commute sQ xQ := by
  have hk : Commute sQ (u (W.K 0)) :=
    of_derivable (Derivable.of (Rel.comm_loc Local.K Local.S 0 2 (by decide))).symm
  have hi : Commute sQ (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .S₂ (by decide))).symm
  simpa only [xQ, W.CX10, W.CX, map_mul] using
    (((hk.mul_right s_d_commute).mul_right s_d_commute).mul_right hk).mul_right hi

theorem s_b_commute : Commute sQ bQ :=
  of_derivable (Derivable.of (Rel.c7 1))

theorem s_swap_commute : Commute sQ swapQ := by
  simpa only [swapQ, swapWord, map_mul] using
    (s_a_commute.mul_right s_x_commute).mul_right s_a_commute

theorem s_c_commute : Commute sQ cQ :=
  (s_swap_commute.mul_right s_b_commute).mul_right s_swap_commute

theorem s_conjugate_commute : Commute sQ (aQ * bQ * aQ) :=
  (s_a_commute.mul_right s_b_commute).mul_right s_a_commute

theorem conj0_b : conj0 bQ = bQ := by
  have hk : Commute bQ (u (W.K 0)) :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hs : Commute bQ (u (W.S 0)) :=
    of_derivable (Derivable.of (Rel.comm_0_12 Local.S)).symm
  have hi : Commute bQ (u W.I) :=
    of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
  have hf : Commute bQ flip0 := by
    simpa only [flip0, W.X, map_mul] using
      (((hk.mul_right hs).mul_right hs).mul_right hk).mul_right hi
  rw [conj0_eq, hf.symm.eq, mul_assoc, flip0_square, mul_one]

theorem conj0_c : conj0 cQ = cQ⁻¹ * sQ := by
  rw [conj0_eq, cQ]
  have hs := inv_of_square swap_square
  have hfs : swapQ * flip0 = flip1 * swapQ := by
    have ht := congrArg (fun v : G => swapQ * v * swapQ) flip0_swap
    simpa only [mul_assoc, show ∀ z : G, swapQ * (swapQ * z) = z from
      fun z => by rw [← mul_assoc, swap_square, one_mul], swap_square, mul_one] using ht
  calc
    flip0 * (swapQ * bQ * swapQ) * flip0 =
        (flip0 * swapQ) * bQ * (swapQ * flip0) := by group
    _ = swapQ * (flip1 * bQ * flip1) * swapQ := by rw [flip0_swap, hfs]; group
    _ = swapQ * (bQ⁻¹ * sQ) * swapQ := by rw [flip1_conjugates_b]
    _ = (swapQ * bQ * swapQ)⁻¹ * sQ := by
      rw [mul_inv_rev, mul_inv_rev, hs]
      rw [mul_assoc, mul_assoc, s_swap_commute.eq]
      group

theorem conj0_conjugate : conj0 (aQ * bQ * aQ) = (aQ * bQ * aQ)⁻¹ * sQ := by
  rw [map_mul, map_mul, conj0_a, conj0_b]
  calc
    flip1 * aQ * bQ * (flip1 * aQ) = aQ * flip1 * bQ * (flip1 * aQ) :=
      congrArg (fun v : G => v * bQ * (flip1 * aQ)) flip1_a_commute.eq
    _ = aQ * (flip1 * bQ * flip1) * aQ := by group
    _ = aQ * (bQ⁻¹ * sQ) * aQ := by rw [flip1_conjugates_b]
    _ = (aQ * bQ * aQ)⁻¹ * sQ := by
      rw [mul_inv_rev, mul_inv_rev, inv_of_square a_square]
      rw [mul_assoc, mul_assoc, s_a_commute.eq]
      group

theorem conj0_ccZ : conj0 (u Cert.ccZ) = u Cert.ccZ * bQ ^ 2 := by
  have hs : u Cert.ccZ * u Cert.ccZ = 1 := by
    simpa only [map_mul, map_one] using of_derivable ccZ_square
  have hi : (u Cert.ccZ)⁻¹ = u Cert.ccZ := inv_of_square hs
  have hmiddle : conj0 (u Cert.ccZ) = cQ * (aQ * bQ * aQ)⁻¹ * bQ⁻¹ := by
    rw [u_ccZ, map_mul, map_mul, map_inv, conj0_c, conj0_conjugate, map_inv, conj0_b]
    rw [mul_inv_rev, inv_inv]
    calc
      sQ⁻¹ * cQ * ((aQ * bQ * aQ)⁻¹ * sQ) * bQ⁻¹ =
          sQ⁻¹ * (cQ * (aQ * bQ * aQ)⁻¹) * sQ * bQ⁻¹ := by group
      _ = (cQ * (aQ * bQ * aQ)⁻¹) * sQ⁻¹ * sQ * bQ⁻¹ := by
        rw [(s_c_commute.mul_right s_conjugate_commute.inv_right).inv_left.eq]
      _ = cQ * (aQ * bQ * aQ)⁻¹ * bQ⁻¹ := by group
  have hform : u Cert.ccZ = bQ * (aQ * bQ * aQ)⁻¹ * cQ := by
    rw [← hi, u_ccZ]
    group
  rw [hmiddle, hform]
  have hbb : bQ * (bQ ^ 2) = bQ⁻¹ := by
    rw [← pow_succ', cube_eq_inv b_fourth]
  rw [mul_assoc cQ (aQ * bQ * aQ)⁻¹ bQ⁻¹,
    mul_assoc (bQ * (aQ * bQ * aQ)⁻¹) cQ (bQ ^ 2),
    mul_assoc bQ (aQ * bQ * aQ)⁻¹ (cQ * bQ ^ 2)]
  rw [b_conjugate_commute.inv_right.left_comm, c_b_commute.symm.left_comm, hbb]
  exact c_conjugate_commute.inv_right.left_comm _

theorem X0_ccZ_flip :
    Derivable Rel (W.X 0 * Cert.ccZ * W.X 0) (Cert.ccZ * W.CS12 ^ 2) := by
  apply to_derivable
  simpa only [map_mul, map_pow, conj0_eq] using conj0_ccZ

def conjSwap : G →* G where
  toFun g := swapQ * g * swapQ⁻¹
  map_one' := by group
  map_mul' g h := by group

theorem conjSwap_eq (g : G) : conjSwap g = swapQ * g * swapQ := by
  change swapQ * g * swapQ⁻¹ = _
  rw [inv_of_square swap_square]

theorem conjSwap_flip0 : conjSwap flip0 = flip1 := by
  rw [conjSwap_eq, mul_assoc, flip0_swap, ← mul_assoc, swap_square, one_mul]

theorem conjSwap_ccZ : conjSwap (u Cert.ccZ) = u Cert.ccZ := by
  rw [conjSwap_eq]
  simpa only [map_mul] using of_derivable swap_ccZ

theorem conjSwap_b : conjSwap bQ = cQ := by rw [conjSwap_eq]; rfl

/-- Flipping wire 1 gives the phase on the other two wires. -/
theorem X1_ccZ_flip :
    Derivable Rel (W.X 1 * Cert.ccZ * W.X 1)
      (Cert.ccZ * (swapWord * W.CS12 * swapWord) ^ 2) := by
  have ht := congrArg conjSwap conj0_ccZ
  rw [conj0_eq, map_mul, map_mul, map_mul, map_pow, conjSwap_flip0,
    conjSwap_ccZ, conjSwap_b] at ht
  apply to_derivable
  simpa only [map_mul, map_pow, cQ] using ht

end
end QCert.CliffordCS3.Three.Monomial
