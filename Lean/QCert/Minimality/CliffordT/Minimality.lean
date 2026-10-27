/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of CliffT₂ (Theorem 37 (4), Figure 8 (d))

The rules of Figure 5 on at most one wire are independent of the others, by
the weighted counts of Figure 8 (d), and so are the two-wire rules (CPh),
(B) and (CZ).  Figure 8 (d) gives no separator for (CSH), (HT²) and (HTH).
-/
import QCert.Minimality.CliffordT.Syntax
import QCert.Minimality.Models

namespace QCert.Minimality.CliffordT

/-- `?ω₈`. -/
def hasω : Weights Gate Occ := ⟨fun _ => Occ.yes, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `?H`. -/
def hasH : Weights Gate Occ := ⟨fun _ => 0, fun | .H => Occ.yes | .T => 0, fun _ => 0, fun _ => 0⟩
/-- `?T`. -/
def hasT : Weights Gate Occ := ⟨fun _ => 0, fun | .T => Occ.yes | .H => 0, fun _ => 0, fun _ => 0⟩
/-- `#{H}_[2]`. -/
def countH : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun | .H => 1 | .T => 0, fun _ => 0, fun _ => 0⟩
/-- `#{H, T, ω₈}_[2]`. -/
def countHTω : Weights Gate (ZMod 2) := ⟨fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0⟩
/-- `?CNOT`. -/
def hasCX : Weights Gate Occ :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => Occ.yes | .swap => 0, fun _ => 0⟩
/-- `#{SWAP}_[2]`. -/
def countSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun | .CX => 0 | .swap => 1, fun _ => 0⟩
/-- `#{CNOT, SWAP}_[2]`. -/
def countCXSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ => 0⟩

/-- Theorem 37 (4): CliffT₂ is minimal up to one wire. -/
theorem minimalUpTo_one : pres.MinimalUpTo 1 := by
  rw [PropPresentation.minimalUpTo_iff]
  intro ρ hρ
  cases ρ with
  | ω8 => exact hasω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | T8 => exact hasT.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | H2 => exact hasH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | E => exact countH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | TX => exact countHTω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | _ => exact absurd hρ (by decide)

/-- Theorem 37, beyond the bound: the two-wire rule (CPh) is independent. -/
theorem independent_CPh : pres.Independent .CPh :=
  hasCX.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)

/-- Theorem 37, beyond the bound: the two-wire rule (B) is independent. -/
theorem independent_B : pres.Independent .B :=
  countSwap.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)

/-- Theorem 37, beyond the bound: the two-wire rule (CZ) is independent. -/
theorem independent_CZ : pres.Independent .CZ :=
  countCXSwap.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)

end QCert.Minimality.CliffordT
