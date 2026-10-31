/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Stabilizer equations for the residual Hadamard atom

The three transpositions on the same target wire but complementary
controls commute with both residuals A and A²P.
-/
import QCert.CliffordCS3.Three.AtomWhiteTransport

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.Cert.KStabilizers

open QuotientGroup LocalKZ AtomTokens
noncomputable section

theorem phase_token0 : Commute P (u (token 0)) := by
  rw [token0_form]
  exact (P_K.mul_right (P_Q.mul_right (Monomial.c_b_commute.symm.pow_right 2))).mul_right P_K.inv_right

theorem phase_token4 : Commute P (u (token 4)) := by
  rw [token4_form]
  exact (P_K.mul_right (P_Q.mul_right (Monomial.b_d_commute.pow_right 2))).mul_right P_K.inv_right

theorem phase_token2 : Commute P (u (token 2)) := by
  rw [token2_form]
  have hs : Commute P S0 := of_derivable (Derivable.of (Rel.comm_0_12 Local.S)).symm
  have hp := ((P_Q.mul_right (Monomial.c_b_commute.symm.pow_right 2)).mul_right
    (Monomial.b_d_commute.pow_right 2)).mul_right (hs.pow_right 2)
  exact (P_K.mul_right hp).mul_right P_K.inv_right

def rule (c : Bool) (d : Fin 7) (ha : Commute A (u (token d)))
    (hp : Commute P (u (token d))) : Rule Rel :=
  if c then
    Rule.ofDerivable ((atom ^ 2 * phase) * token d) (token d * (atom ^ 2 * phase))
      (to_derivable (by simpa only [map_mul, map_pow] using ((ha.pow_left 2).mul_left hp).eq))
  else
    Rule.ofDerivable (atom * token d) (token d * atom)
      (to_derivable (by simpa only [map_mul] using ha.eq))

def table (c : Bool) : List (Rule Rel) :=
  [rule c 0 atom_token0 phase_token0,
   rule c 2 atom_token2 phase_token2,
   rule c 4 atom_token4 phase_token4]

def indices : List ℕ := [29, 33, 37]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.KStabilizers
