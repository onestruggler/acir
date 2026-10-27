/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of RCliff₂ (Section 3.1)

The common qubit interpretation (`QCert.Minimality.Qubit`) restricted to the
gates of RCliff₂: `⟦-⟧ = -1`, `⟦H⟧`, `⟦Z⟧`, `⟦CNOT⟧`, and the swap.
`ops`/`scaled` give the same gates over ℤ[ω], the Hadamard scaled by `√2`.
-/
import QCert.Minimality.RealClifford.Syntax
import QCert.Minimality.Qubit

namespace QCert.Minimality.RealClifford

open Matrix Qubit

/-- The gates of RCliff₂ over ℤ[ω], the Hadamard scaled by `√2`. -/
def ops : GateOps Gate ZOmega 2 where
  scalar _ := -1
  gate1
    | .H => hadZ
    | .Z => zZ
  gate2
    | .CX => cnotZ
    | .swap => swapZ
  gate3 g := nomatch g

/-- The scaling: only `H` carries a factor `1/√2`. -/
def scaled : ScaledOps Gate ZOmega 2 where
  ops := ops
  e1
    | .H => 1
    | .Z => 0
  e2 _ := 0
  e3 g := nomatch g

/-- The interpretation of the gates of RCliff₂ (Section 3.1). -/
noncomputable def sem : GateSem Gate ℂ 2 where
  scalar
    | .minus => ⟨-1, minus_one_mem⟩
  gate1
    | .H => ⟨hadamardC, hadamardC_mem⟩
    | .Z => ⟨zC, zC_mem⟩
  gate2
    | .CX => ⟨cnotC, cnotC_mem⟩
    | .swap => ⟨swapC, swapC_mem⟩
  gate3 g := nomatch g

theorem sem_toOps : sem.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; show (-1 : ℂ) = ZOmega.toC (-1); simp
  · funext g; cases g
    · exact hadamardC_eq
    · exact zC_eq
  · funext g; cases g
    · exact cnotC_eq
    · exact swapC_eq
  · funext g; exact nomatch g

end QCert.Minimality.RealClifford
