/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The residual Clifford group on the last two basis states

The finite four-letter certificates are transported through the first
wire swap. They give the local K/Z relations without semantic axioms.
-/
import QCert.CliffordCS3.Three.Cert.AtomRelations
import QCert.CliffordCS3.Three.Conjugation
import QCert.CliffordCS3.Three.PhaseSymmetry
import QCert.CliffordCS3.Three.KOrder

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.LocalKZ

open QuotientGroup
noncomputable section

abbrev A : G := u Cert.atom
abbrev Q : G := u Cert.ccZ
abbrev P : G := u phase
abbrev T : G := u (Cert.token 6)
abbrev K : G := u (W.K 0)
abbrev S : G := Monomial.swapQ
abbrev C : G := Monomial.cQ
abbrev R : G := u Cert.AtomRelations.signCore
abbrev AM : G := u Cert.AtomRelations.word

theorem S_square : S * S = 1 := Monomial.swap_square

def sw : G →* G where
  toFun x := S * x * S
  map_one' := by simp only [mul_one, S_square]
  map_mul' x y := by
    simp only [mul_assoc]
    rw [show S * (S * (y * S)) = y * S by rw [← mul_assoc, S_square, one_mul]]

theorem sw_A : sw AM = A := by
  have h : Derivable Rel
      (Swap01.word * Swap01.middleAtom * Swap01.word) Cert.atom := by
    apply Swap01.of_q
    simpa only [map_mul] using Swap01.swap_atom
  exact of_derivable h

theorem sw_C : sw C = P := by
  change S * (S * P * S) * S = P
  have hs (z : G) : S * (S * z) = z := by rw [← mul_assoc, S_square, one_mul]
  simp only [mul_assoc, hs, S_square, mul_one]

theorem sw_Q : sw Q = Q := of_derivable Monomial.swap_ccZ

theorem R_eq : R = C * Q := by
  change R = C * u Cert.ccZ
  rw [Monomial.u_ccZ]
  have hr : R = Monomial.aQ * P * Monomial.aQ * P⁻¹ := by
    change u (W.CX01 * W.CS12 * W.CX01 * W.CS12 ^ 3) = _
    simp only [map_mul, map_pow, Monomial.cube_eq_inv Monomial.b_fourth]
    rfl
  rw [hr]
  group <;> rfl

theorem sw_R : sw R = P * Q := by rw [R_eq, map_mul, sw_C, sw_Q]

theorem sw_K : sw (u (W.K 1)) = K := of_derivable Swap01.conjugate_K

theorem K_inv (n : Fin 3) : u (W.I * W.K n) = (u (W.K n))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul, map_one] using of_derivable (K_inverse' n)

theorem sw_Kinv : sw (u (W.I * W.K 1)) = K⁻¹ := by rw [K_inv, map_inv, sw_K]

theorem sw_phaseSquare : sw (u Cert.AtomRelations.phaseSquare) = P ^ 2 := by
  have h : Derivable Rel
      (Swap01.word * Cert.AtomCube.phaseSquare * Swap01.word) (phase ^ 2) := by
    apply Swap01.of_q
    simpa only [map_mul] using Swap01.swap_phaseSquare
  exact of_derivable h

theorem P_A : Commute P A := by
  have h := atom_phase_commute_of Monomial.phase_CS02_commute
  change u phase * u Cert.atom = u Cert.atom * u phase
  rw [← map_mul, ← map_mul]
  exact of_derivable (Swap01.of_q (by simpa only [map_mul] using h.eq))

theorem P_Q : Commute P Q := of_derivable Monomial.phase_ccZ_commute

theorem P_K : Commute P K :=
  of_derivable (Derivable.of (Rel.comm_0_12 Local.K)).symm

theorem P_fourth : P ^ 4 = 1 := by
  simpa only [map_pow, map_one] using of_derivable (Derivable.of (Rel.c5 1))

theorem A_cube : A ^ 3 = P ^ 2 := by
  simpa only [map_pow] using of_derivable Swap01.atom_cube

theorem Q_square : Q * Q = 1 := by
  simpa only [map_mul, map_one] using of_derivable Monomial.ccZ_square

theorem T_eq : T = K * Q * K⁻¹ := by
  change u (W.K 0 * Cert.ccZ * (W.I * W.K 0)) = _
  rw [map_mul, K_inv, map_mul]

theorem A_Q : A * Q = T * A := by
  have h := congrArg sw (of_derivable Cert.AtomRelations.conjugate_sign)
  have hi : sw (u W.I) = u W.I := of_derivable Swap01.conjugate_I
  have hik : u W.I * K = K⁻¹ := by simpa only [map_mul] using K_inv 0
  simp only [map_mul, sw_A, sw_R, sw_K, hi, hik] at h
  apply mul_left_cancel (a := P)
  calc
    P * (A * Q) = A * (P * Q) := by rw [← mul_assoc, P_A.eq, mul_assoc]
    _ = K * (P * Q) * K⁻¹ * A := h
    _ = P * (K * Q * K⁻¹ * A) := by
      rw [← mul_assoc K P Q, P_K.symm.eq]
      group
    _ = P * (T * A) := by rw [T_eq]

theorem QA_cube : (Q * A) ^ 3 = P ^ 3 := by
  have h := congrArg sw (of_derivable Cert.AtomRelations.triangle)
  simp only [map_pow, map_mul, sw_R, sw_A, sw_phaseSquare] at h
  have hc : Commute P (Q * A) := P_Q.mul_right P_A
  have hh : P ^ 3 * (Q * A) ^ 3 = P ^ 2 := by
    rw [← hc.mul_pow]
    simpa only [mul_assoc] using h
  apply mul_left_cancel (a := P ^ 3)
  rw [hh]
  calc
    P ^ 2 = P ^ 4 * P ^ 2 := by rw [P_fourth, one_mul]
    _ = P ^ 3 * P ^ 3 := by group

theorem atom_sign : Derivable Rel (Cert.atom * Cert.ccZ) (Cert.token 6 * Cert.atom) := by
  apply to_derivable
  simpa only [map_mul] using A_Q

theorem sign_atom_cube : Derivable Rel ((Cert.ccZ * Cert.atom) ^ 3) (phase ^ 3) := by
  apply to_derivable
  simpa only [map_mul, map_pow] using QA_cube

theorem A_sixth : A ^ 6 = 1 := by
  calc
    A ^ 6 = (A ^ 3) ^ 2 := by rw [← pow_mul]
    _ = (P ^ 2) ^ 2 := by rw [A_cube]
    _ = 1 := by rw [← pow_mul]; exact P_fourth

theorem A_inv : A⁻¹ = A ^ 5 := by
  symm
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using A_sixth

theorem token_as_atoms :
    Derivable Rel (Cert.token 6) (Cert.atom * Cert.ccZ * Cert.atom ^ 5) := by
  apply to_derivable
  simp only [map_mul, map_pow]
  rw [← A_inv]
  have h := A_Q
  calc
    T = (T * A) * A⁻¹ := by group
    _ = A * Q * A⁻¹ := by rw [← h]

end
end QCert.CliffordCS3.Three.LocalKZ
