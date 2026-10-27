/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of Cliff₂ (Section 3.1)

The common qubit interpretation (`QCert.Minimality.Qubit`) restricted to the
gates of Cliff₂: `⟦ω₈⟧ = e^{iπ/4}`, `⟦H⟧`, `⟦S⟧`, `⟦CNOT⟧`, and the swap.
`ops`/`scaled` give the same gates over ℤ[ω], the Hadamard scaled by `√2`,
and `sem_toOps` identifies the two.
-/
import QCert.Minimality.Clifford.Syntax
import QCert.Minimality.Qubit

namespace QCert.Minimality.Clifford

open Matrix Qubit

/-- The gates of Cliff₂ over ℤ[ω], the Hadamard scaled by `√2`. -/
def ops : GateOps Gate ZOmega 2 where
  scalar _ := ZOmega.ω
  gate1
    | .H => hadZ
    | .S => sZ
  gate2
    | .CX => cnotZ
    | .swap => swapZ
  gate3 g := nomatch g

/-- The scaling: only `H` carries a factor `1/√2`. -/
def scaled : ScaledOps Gate ZOmega 2 where
  ops := ops
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

/-- The interpretation of the gates of Cliff₂ (Section 3.1). -/
noncomputable def sem : GateSem Gate ℂ 2 where
  scalar
    | .ω => ⟨QCert.ω, ω_mem⟩
  gate1
    | .H => ⟨hadamardC, hadamardC_mem⟩
    | .S => ⟨sC, sC_mem⟩
  gate2
    | .CX => ⟨cnotC, cnotC_mem⟩
    | .swap => ⟨swapC, swapC_mem⟩
  gate3 g := nomatch g

theorem sem_toOps : sem.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZOmega.toC_X.symm
  · funext g; cases g
    · exact hadamardC_eq
    · exact sC_eq
  · funext g; cases g
    · exact cnotC_eq
    · exact swapC_eq
  · funext g; exact nomatch g

end QCert.Minimality.Clifford
