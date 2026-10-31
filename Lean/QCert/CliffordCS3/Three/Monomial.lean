/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The three-qubit controlled sign

The involution law is derived from C12–C15 and checked two-qubit
identities. In particular, no three-qubit completeness assumption is used.
-/
import QCert.CliffordCS3.Three.QuotientGroup
import QCert.CliffordCS3.Three.MonomialAlgebra
import QCert.CliffordCS3.Three.Cert.Words
import QCert.CliffordCS3.Three.TokenInvolutions

set_option maxRecDepth 10000

namespace QCert.CliffordCS3.Three.Monomial

open QuotientGroup
noncomputable section

abbrev aQ : G := u W.CX01
abbrev xQ : G := u W.CX10
abbrev bQ : G := u W.CS12
abbrev dQ : G := u W.CS01
abbrev yQ : G := u W.CX21
abbrev sQ : G := u (W.S 2)

def swapWord : Word Gen := W.CX01 * W.CX10 * W.CX01
abbrev swapQ : G := u swapWord
def cQ : G := swapQ * bQ * swapQ

private def cu : Word Two.Gen2 := Two.W2.Ku * Two.W2.CS * Two.W2.CS * Two.W2.Ku * Two.W2.I
private def cl : Word Two.Gen2 := Two.W2.Kl * Two.W2.CS * Two.W2.CS * Two.W2.Kl * Two.W2.I

theorem a_square : aQ * aQ = 1 := by
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := cl * cl) (v := 1) (by decide +kernel)))
  simpa [aQ, cl, W.CX01, W.CX, Two.embW, Two.emb] using h

theorem x_square : xQ * xQ = 1 := by
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := cu * cu) (v := 1) (by decide +kernel)))
  simpa [xQ, cu, W.CX10, W.CX, Two.embW, Two.emb] using h

theorem y_square : yQ * yQ = 1 := by
  have h := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := cu * cu) (v := 1) (by decide +kernel)))
  simpa [yQ, cu, W.CX21, W.CX, Two.embW, Two.emb] using h

theorem cnot_braid : aQ * xQ * aQ = xQ * aQ * xQ := by
  have h := of_derivable (Two.derivable_embed 0 (Two.derivable_of_check2
    (w := cl * cu * cl) (v := cu * cl * cu) (by decide +kernel)))
  simpa [aQ, xQ, cu, cl, W.CX01, W.CX10, W.CX, Two.embW, Two.emb] using h

theorem b_fourth : bQ ^ 4 = 1 := by
  simpa only [map_pow, map_one] using of_derivable (Derivable.of (Rel.c5 1))

theorem d_fourth : dQ ^ 4 = 1 := by
  simpa only [map_pow, map_one] using of_derivable (Derivable.of (Rel.c5 0))

theorem cube_eq_inv {v : G} (hv : v ^ 4 = 1) : v ^ 3 = v⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using hv

theorem b_d_commute : Commute bQ dQ := by
  exact of_derivable (Derivable.of Rel.c12)

theorem s_d_commute : Commute sQ dQ := by
  exact of_derivable (Derivable.of (Rel.comm_2_01 Local.S))

theorem b_x_commute : Commute bQ xQ := by
  have hk : Commute bQ (u (W.K 0)) := by
    exact of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hi : Commute bQ (u W.I) := by
    exact of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
  simpa only [xQ, W.CX10, W.CX, map_mul] using
    (((hk.mul_right b_d_commute).mul_right b_d_commute).mul_right hk).mul_right hi

theorem y_conjugates_b : yQ * bQ * yQ = bQ⁻¹ * sQ := by
  have h := of_derivable (Two.derivable_embed 1 (Two.derivable_of_check2
    (w := cu * Two.W2.CS * cu) (v := Two.W2.CS ^ 3 * Two.W2.Sl)
    (by decide +kernel)))
  have h' : yQ * bQ * yQ = bQ ^ 3 * sQ := by
    simpa [yQ, bQ, sQ, cu, W.CX21, W.CX, Two.embW, Two.emb] using h
  rwa [cube_eq_inv b_fourth] at h'

theorem c14 : bQ * aQ * bQ⁻¹ * aQ = dQ * yQ * dQ⁻¹ * yQ := by
  have h := of_derivable (Derivable.of Rel.c14)
  simpa only [map_mul, map_pow, cube_eq_inv b_fourth, cube_eq_inv d_fourth] using h

theorem b_conjugate_commute : Commute bQ (aQ * bQ * aQ) :=
  commute_phase_conjugate a_square y_square b_d_commute s_d_commute y_conjugates_b c14

theorem c_as_conjugate : cQ = xQ * aQ * bQ * aQ * xQ := by
  have hswap : swapQ = xQ * aQ * xQ := by
    simpa only [swapQ, swapWord, map_mul] using cnot_braid
  rw [cQ, hswap]
  have hxb : xQ * bQ * xQ = bQ := by
    calc
      xQ * bQ * xQ = bQ * (xQ * xQ) := by rw [b_x_commute.symm.eq]; group
      _ = bQ := by rw [x_square, mul_one]
  calc
    (xQ * aQ * xQ) * bQ * (xQ * aQ * xQ) =
        xQ * aQ * (xQ * bQ * xQ) * aQ * xQ := by group
    _ = xQ * aQ * bQ * aQ * xQ := by rw [hxb]

theorem swap_square : swapQ * swapQ = 1 := by
  change (aQ * xQ * aQ) * (aQ * xQ * aQ) = 1
  have haa (z : G) : aQ * (aQ * z) = z := by rw [← mul_assoc, a_square, one_mul]
  have hxx (z : G) : xQ * (xQ * z) = z := by rw [← mul_assoc, x_square, one_mul]
  simp only [mul_assoc, haa, hxx, a_square]

theorem u_ccZ : u Cert.ccZ = cQ⁻¹ * (aQ * bQ * aQ) * bQ⁻¹ := by
  have hdef : Cert.ccZ = swapWord * W.CS12 ^ 3 * swapWord *
      W.CX01 * W.CS12 * W.CX01 * W.CS12 ^ 3 := rfl
  rw [hdef, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow]
  rw [cube_eq_inv b_fourth]
  rw [cQ, mul_inv_rev, mul_inv_rev, inv_of_square swap_square]
  group

theorem ccZ_square : Derivable Rel (Cert.ccZ * Cert.ccZ) 1 := by
  apply to_derivable
  rw [map_mul, map_one, u_ccZ]
  have h15 : xQ * aQ * bQ ^ 2 * aQ * xQ = aQ * bQ ^ 2 * aQ * bQ ^ 2 := by
    simpa only [map_mul, map_pow] using of_derivable (Derivable.of Rel.c15)
  simpa only [sq] using triple_phase_square a_square x_square cnot_braid
    b_x_commute b_conjugate_commute c_as_conjugate h15 b_fourth

theorem c_b_commute : Commute cQ bQ := by
  have h := b_conjugate_commute.symm.conj xQ
  rw [inv_of_square x_square] at h
  have hxb : xQ * bQ * xQ = bQ := by
    calc
      xQ * bQ * xQ = bQ * (xQ * xQ) := by rw [b_x_commute.symm.eq]; group
      _ = bQ := by rw [x_square, mul_one]
  rw [hxb] at h
  simpa only [c_as_conjugate, mul_assoc] using h

theorem phase_ccZ_commute :
    Derivable Rel (W.CS12 * Cert.ccZ) (Cert.ccZ * W.CS12) := by
  apply to_derivable
  simp only [map_mul, u_ccZ]
  exact ((c_b_commute.symm.inv_right).mul_right b_conjugate_commute).mul_right
    (Commute.refl bQ).inv_right

theorem phase_CS02_commute :
    Derivable Rel (W.CS12 * (swapWord * W.CS12 * swapWord))
      ((swapWord * W.CS12 * swapWord) * W.CS12) := by
  apply to_derivable
  simpa only [map_mul, cQ, swapQ] using c_b_commute.symm.eq

theorem phase_token6_commute :
    Derivable Rel (Cert.token 6 * W.CS12) (W.CS12 * Cert.token 6) := by
  apply to_derivable
  have hK : Commute bQ (u (W.K 0)) := by
    exact of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm
  have hI : Commute bQ (u W.I) := by
    exact of_derivable (Derivable.of (Rel.comm_i .CS₁₂ (by decide))).symm
  have hQ : Commute bQ (u Cert.ccZ) := of_derivable phase_ccZ_commute
  have h := ((hK.mul_right hQ).mul_right (hI.mul_right hK)).symm
  simpa only [← map_mul] using h

end
end QCert.CliffordCS3.Three.Monomial

