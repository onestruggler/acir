/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of CNOTdihe₂ (Section 3.1)

The common qubit interpretation (`QCert.Minimality.Qubit`) restricted to the
gates of CNOTdihe₂: `⟦ω₈⟧ = e^{iπ/4}`, `⟦X⟧`, `⟦T⟧`, `⟦CNOT⟧`, and the
swap.  All entries lie in ℤ[ω], with no scaling.
-/
import QCert.Minimality.CNOTDihedral.Syntax
import QCert.Minimality.Qubit

namespace QCert.Minimality.CNOTDihedral

open Matrix Qubit

/-- The gates of CNOTdihe₂ over ℤ[ω]. -/
def ops : GateOps Gate ZOmega 2 where
  scalar _ := ZOmega.ω
  gate1
    | .X => xZ
    | .T => tZ
  gate2
    | .CX => cnotZ
    | .swap => swapZ
  gate3 g := nomatch g

/-- No gate is scaled. -/
def scaled : ScaledOps Gate ZOmega 2 where
  ops := ops
  e1 _ := 0
  e2 _ := 0
  e3 g := nomatch g

/-- The interpretation of the gates of CNOTdihe₂ (Section 3.1). -/
noncomputable def sem : GateSem Gate ℂ 2 where
  scalar
    | .ω => ⟨QCert.ω, ω_mem⟩
  gate1
    | .X => ⟨xC, xC_mem⟩
    | .T => ⟨tC, tC_mem⟩
  gate2
    | .CX => ⟨cnotC, cnotC_mem⟩
    | .swap => ⟨swapC, swapC_mem⟩
  gate3 g := nomatch g

theorem sem_toOps : sem.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZOmega.toC_X.symm
  · funext g; cases g
    · exact xC_eq
    · exact tC_eq
  · funext g; cases g
    · exact cnotC_eq
    · exact swapC_eq
  · funext g; exact nomatch g

end QCert.Minimality.CNOTDihedral
