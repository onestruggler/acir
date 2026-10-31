/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Disjoint residual Hadamards, in both cosets
-/
import QCert.CliffordCS3.Three.BlockHorizontal
import QCert.CliffordCS3.Three.PhaseOppositeSupport
import QCert.CliffordCS3.Three.GaugeFacts

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.Cert.DisjointK

open QuotientGroup LocalKZ BlockHorizontal RestrictedGauge
noncomputable section

theorem disjoint : Commute L (F * L * F⁻¹) := by
  rw [frame_L]
  have ha : Commute L barA :=
    opposite_atoms.mul_left PhaseOppositeSupport.C_opposite_atom
  have hc : Commute C (C * D * Q) :=
    ((Commute.refl C).mul_right Monomial.c_d_commute).mul_right AtomTokens.C_Q
  have hp : Commute L (C * D * Q) :=
    (phase_frame_commutes PhaseGaugeSupport.r_A).symm.mul_left hc
  exact ha.mul_right hp

def lhs : List Letter :=
  [.k, .t4, .t5, .t6, .t4, .t5, .k, .t5, .t4, .t6, .t5, .t4]
def rhs : List Letter :=
  [.t4, .t5, .t6, .t4, .t5, .k, .t5, .t4, .t6, .t5, .t4, .k]

theorem frame_inv : F⁻¹ =
    u (Cert.token 5) * u (Cert.token 4) * T * u (Cert.token 5) * u (Cert.token 4) := by
  have hi (d : Fin 7) : (u (Cert.token d))⁻¹ = u (Cert.token d) := by
    apply Monomial.inv_of_square
    simpa only [map_mul, map_one] using of_derivable (token_involution d)
  change (u (Cert.token 4) * (u (Cert.token 5) * (T *
    (u (Cert.token 4) * (u (Cert.token 5) * 1)))))⁻¹ = _
  simp only [mul_one, mul_inv_rev, hi, T, mul_assoc]

theorem lifted : Gauge.eval lift lhs = Gauge.eval lift rhs := by
  have ht := disjoint.eq
  rw [frame_inv] at ht
  have hF : F = u (Cert.token 4) * u (Cert.token 5) * T *
      u (Cert.token 4) * u (Cert.token 5) := by
    change u (Cert.token 4) * (u (Cert.token 5) * (T *
      (u (Cert.token 4) * (u (Cert.token 5) * 1)))) = _
    simp only [mul_one, mul_assoc]
  rw [hF] at ht
  simpa only [Gauge.eval, lhs, rhs, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, lift, L, mul_one, mul_assoc] using ht

def rule (c : Bool) : Rule Rel :=
  Rule.ofDerivable (hstar h c (word lhs)).1 (hstar h c (word rhs)).1
    (residuals_equal facts c lhs rhs 1 (by decide) (by decide) lifted)

def table (c : Bool) : List (Rule Rel) := [rule c]
def indices : List ℕ := [43]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.DisjointK
