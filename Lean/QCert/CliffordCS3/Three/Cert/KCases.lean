/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# All five complementary exchanges commute with the residual Hadamard
-/
import QCert.CliffordCS3.Three.AtomDoubleWhite

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.Cert.KCases

noncomputable section

def table (c : Bool) : List (Rule Rel) :=
  KStabilizers.table c ++
    [KStabilizers.rule c 1 AtomDoubleWhite.atom_token1 PhaseStabilizers.phase_token1,
     KStabilizers.rule c 3 AtomCross.atom_token3 PhaseStabilizers.phase_token3]

def indices : List ℕ := [29, 31, 33, 35, 37]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.KCases
