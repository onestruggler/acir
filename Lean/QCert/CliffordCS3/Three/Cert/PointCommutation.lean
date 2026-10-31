/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The disjoint phase/Hadamard macro axiom, in both cosets
-/
import QCert.CliffordCS3.Three.PointCommutation
import QCert.CliffordCS3.Three.GaugeFacts

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.Cert.PointCommutation

open RestrictedGauge
noncomputable section

def lhs : List Letter := [.t5, .t6, .z, .t6, .t5, .k]
def rhs : List Letter := [.k, .t5, .t6, .z, .t6, .t5]

theorem lifted : Gauge.eval lift lhs = Gauge.eval lift rhs := by
  simpa only [Gauge.eval, lhs, rhs, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, lift, mul_one, mul_assoc] using
      Three.PointCommutation.point_block.eq

def rule (c : Bool) : Rule Rel :=
  Rule.ofDerivable (hstar h c (word lhs)).1 (hstar h c (word rhs)).1
    (residuals_equal facts c lhs rhs 1 (by decide) (by decide) lifted)

def table (c : Bool) : List (Rule Rel) := [rule c]

def indices : List ℕ := [42]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.PointCommutation
