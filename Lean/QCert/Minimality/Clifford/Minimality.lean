/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of Cliff₂ (Theorem 37 (1), Figure 8 (a))

Each rule of Figure 2 is independent of the others, by the separator of
Figure 8 (a), a weighted count; by the truncation of Remark 14 only the
rules on at most as many wires need be equalised.
-/
import QCert.Minimality.Clifford.Syntax
import QCert.Minimality.Models

namespace QCert.Minimality.Clifford

/-- `?ω₈`. -/
def hasω : Weights Gate Occ := ⟨fun _ => Occ.yes, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- `?H`. -/
def hasH : Weights Gate Occ := ⟨fun _ => 0, fun | .H => Occ.yes | .S => 0, fun _ => 0, fun _ => 0⟩

/-- `?S`. -/
def hasS : Weights Gate Occ := ⟨fun _ => 0, fun | .S => Occ.yes | .H => 0, fun _ => 0, fun _ => 0⟩

/-- `#{H}_[2]`. -/
def countH : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun | .H => 1 | .S => 0, fun _ => 0, fun _ => 0⟩

/-- `?CNOT`. -/
def hasCX : Weights Gate Occ :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => Occ.yes | .swap => 0, fun _ => 0⟩

/-- `#{SWAP}_[2]`: the structural swap counted. -/
def countSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun | .CX => 0 | .swap => 1, fun _ => 0⟩

/-- `#{CNOT, SWAP}_[2]`. -/
def countCXSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 0⟩

/-- `arg det₂` (Definition 35) in units of `π/4`: a gate `g` on `n` wires
weighs `2^{2-n} arg det ⟦g⟧`; `det ⟦ω₈⟧ = e^{iπ/4}`, `det ⟦H⟧ = -1`,
`det ⟦S⟧ = i`, `det ⟦CNOT⟧ = -1`, and the swap weighs `ε₂ = π`. -/
def argdet2 : Weights Gate (ZMod 8) :=
  ⟨fun _ => 4, fun | .H => 0 | .S => 4, fun | .CX => 4 | .swap => 4, fun _ => 0⟩

/-- Theorem 37 (1): Cliff₂ is minimal (in all arities). -/
theorem minimal : pres.Minimal
  | .ω8 => hasω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .H2 => hasH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .S4 => hasS.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .E => countH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .CPh => hasCX.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .B => countSwap.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .CZ => countCXSwap.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .I => argdet2.independent rfl _ (by intro a; cases a <;> decide) (by decide)

end QCert.Minimality.Clifford
