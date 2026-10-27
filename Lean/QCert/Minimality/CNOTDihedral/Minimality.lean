/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of CNOTdihe₂ (Theorem 37 (6), Figure 8 (f))

Each rule of Figure 7 is independent of the others, by the weighted counts
of Figure 8 (f).
-/
import QCert.Minimality.CNOTDihedral.Syntax
import QCert.Minimality.Models

namespace QCert.Minimality.CNOTDihedral

/-- `?ω₈`. -/
def hasω : Weights Gate Occ := ⟨fun _ => Occ.yes, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `?T`. -/
def hasT : Weights Gate Occ := ⟨fun _ => 0, fun | .T => Occ.yes | .X => 0, fun _ => 0, fun _ => 0⟩
/-- `?X`. -/
def hasX : Weights Gate Occ := ⟨fun _ => 0, fun | .X => Occ.yes | .T => 0, fun _ => 0, fun _ => 0⟩
/-- `#{ω₈}_[2]`. -/
def countω : Weights Gate (ZMod 2) := ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `#{X}_[2]`. -/
def countX : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun | .X => 1 | .T => 0, fun _ => 0, fun _ => 0⟩
/-- `?CNOT`. -/
def hasCX : Weights Gate Occ :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => Occ.yes | .swap => 0, fun _ => 0⟩
/-- `#{SWAP}_[2]`. -/
def countSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun | .CX => 0 | .swap => 1, fun _ => 0⟩
/-- `#{T, ω₈, ω₈}_[8]`: `T` counts once and `ω₈` twice. -/
def countTωω8 : Weights Gate (ZMod 8) := ⟨fun _ => 2, fun | .T => 1 | .X => 0, fun _ => 0, fun _ => 0⟩
/-- `#{CNOT, SWAP}_[2]`. -/
def countCXSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 0⟩
/-- `#{T, ω₈, ω₈}_[4]`. -/
def countTωω4 : Weights Gate (ZMod 4) := ⟨fun _ => 2, fun | .T => 1 | .X => 0, fun _ => 0, fun _ => 0⟩
/-- `arg det₃` in units of `π/4`: a gate on `n` wires weighs
`2^{3-n} arg det`; `det ⟦ω₈⟧ = e^{iπ/4}` weighs `8 = 0`,
`det ⟦X⟧ = -1` weighs `4 · 4 = 0`, `det ⟦T⟧ = e^{iπ/4}` weighs `4`,
`det ⟦CNOT⟧ = -1` weighs `2 · 4 = 0`, and the swap `ε₃ = 0`. -/
def argdet3 : Weights Gate (ZMod 8) := ⟨fun _ => 0, fun | .T => 4 | .X => 0, fun _ => 0, fun _ => 0⟩

/-- Theorem 37 (6): CNOTdihe₂ is minimal (in all arities). -/
theorem minimal : pres.Minimal
  | .ω8 => hasω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .X2 => hasX.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .T8 => hasT.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .TX => countω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .XC => countX.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .B => countSwap.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .ZC => countTωω8.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .CPh => hasCX.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .I => countCXSwap.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | .C2T => countTωω4.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | .C3T => argdet3.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)

end QCert.Minimality.CNOTDihedral
