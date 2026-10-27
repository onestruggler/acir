/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of Cliff₃ (Section 3.2)

The qutrit interpretation of Definition 17 (`QCert.Minimality.Qutrit`):
`⟦ω₁₂⟧ = e^{iπ/6}`, `⟦H⟧`, `⟦S⟧`, `⟦CNOT⟧`, and the swap.  `ops`/`scaled`
give the same gates over ℤ[ζ₁₂], the Hadamard scaled by `√3`.
-/
import QCert.Minimality.QutritClifford.Syntax
import QCert.Minimality.Qutrit

namespace QCert.Minimality.QutritClifford

open Matrix Qutrit

/-- The gates of Cliff₃ over ℤ[ζ₁₂], the Hadamard scaled by `√3`. -/
def ops : GateOps Gate ZZeta 3 where
  scalar _ := ZZeta.ζ
  gate1
    | .H => hadZ
    | .S => sZ
  gate2
    | .CX => cnotZ
    | .swap => swapZ
  gate3 g := nomatch g

/-- The scaling: only `H` carries a factor `1/√3`. -/
def scaled : ScaledOps Gate ZZeta 3 where
  ops := ops
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

/-- The interpretation of the gates of Cliff₃ (Definition 17). -/
noncomputable def sem : GateSem Gate ℂ 3 where
  scalar
    | .ω => ⟨ZZeta.ζ12, ζ12_mem⟩
  gate1
    | .H => ⟨hadamardC, hadamardC_mem⟩
    | .S => ⟨sC, sC_mem⟩
  gate2
    | .CX => ⟨cnotC, cnotC_mem⟩
    | .swap => ⟨swapC, swapC_mem⟩
  gate3 g := nomatch g

theorem sem_toOps : sem.toOps = scaled.toOps ZZeta.toC invSqrt3 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZZeta.toC_X.symm
  · funext g; cases g
    · exact hadamardC_eq
    · exact sC_eq
  · funext g; cases g
    · exact cnotC_eq
    · exact swapC_eq
  · funext g; exact nomatch g

end QCert.Minimality.QutritClifford
