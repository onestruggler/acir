/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of Cliff₃ (Theorem 37 (3), Figure 8 (c))

The rules of Figure 4 on at most two wires are independent of the others, by
the separators of Figure 8 (c): weighted counts, and for (SS') the projective
substitution `[S := SX]∼` (Proposition 38; `SX` is `S` followed by `X`),
realised as matrices over ℚ(ζ₁₂) modulo units.  Figure 8 (c) gives no
separator for (I).
-/
import QCert.Minimality.QutritClifford.Semantics
import QCert.Minimality.Models

namespace QCert.Minimality.QutritClifford

open Qutrit

/-- `?ω₁₂`. -/
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
/-- `#{SWAP}_[2]`. -/
def countSwap : Weights Gate (ZMod 2) :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => 0 | .swap => 1, fun _ => 0⟩
/-- `#{S}_[3]`. -/
def countS : Weights Gate (ZMod 3) := ⟨fun _ => 0, fun | .S => 1 | .H => 0, fun _ => 0, fun _ => 0⟩
/-- `#{CNOT}_[2]`. -/
def countCX : Weights Gate (ZMod 2) :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => 1 | .swap => 0, fun _ => 0⟩

/-- The matrix of `S` followed by `X`: `|x⟩ ↦ ζ₁₂^{2x(x-1)} |x + 1⟩`. -/
def sxZ : Op ZZeta 3 1 := fun s t =>
  if (s 0 : ℕ) = ((t 0 : ℕ) + 1) % 3 then ZZeta.ζ ^ (2 * ((t 0 : ℕ) * ((t 0 : ℕ) - 1))) else 0

/-- `sxZ` is the matrix of the circuit `S ; X` (`X := H Z H³`, eight
Hadamards, so the integer matrix is `√3⁸ = 81` times it). -/
theorem sxZ_eq : (81 : ZZeta) • sxZ = ops.eval 1 (seq [S, X]) := by
  rw [← den_matRows sxZ, ← LinRep.den_smul, ← den_evalRows]
  exact congrArg _ (by decide +kernel)

/-- `[S := SX]∼`. -/
def substS : ScaledOps Gate ZZeta 3 where
  ops := { ops with gate1 := fun | .H => hadZ | .S => sxZ }
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

theorem substS_sym {k : ℕ} {w v : Circuit Gate k} :
    Sym pres.swap k w v → substS.ops.eval k w = substS.ops.eval k v
  | .invol => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .H => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .S => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .CX => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .swap => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat3 g => nomatch g

/-- Proposition 38: (SS') is independent, by `[S := SX]∼`. -/
theorem independent_SS' : pres.Independent .SS' :=
  independent_of_proj ZZeta.toQ ZZeta.toQ_injective substS.ops substS_sym .SS'
    (fun a ha hne => by
      cases a with
      | ω12 => exact projHyp substS (ZZeta.ζ ^ 0) (ZZeta.isUnit_toQ_ζ_pow 0) (by decide +kernel)
      | H4 => exact projHyp substS (ZZeta.ζ ^ 0) (ZZeta.isUnit_toQ_ζ_pow 0) (by decide +kernel)
      | S3 => exact projHyp substS (ZZeta.ζ ^ 4) (ZZeta.isUnit_toQ_ζ_pow 4) (by decide +kernel)
      | E => exact projHyp substS (ZZeta.ζ ^ 8) (ZZeta.isUnit_toQ_ζ_pow 8) (by decide +kernel)
      | SS' => exact absurd rfl hne
      | _ => exact absurd ha (by decide))
    ⟨![0], ![0], ![1], ![1], by simp only [eval_apply_eq substS.ops]; decide +kernel⟩

/-- Theorem 37 (3): Cliff₃ is minimal up to two qutrit wires. -/
theorem minimalUpTo_two : pres.MinimalUpTo 2 := by
  rw [PropPresentation.minimalUpTo_iff]
  intro ρ hρ
  cases ρ with
  | ω12 => exact hasω.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | H4 => exact hasH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | S3 => exact hasS.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | E => exact countH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | SS' => exact independent_SS'
  | CPh =>
    exact hasCX.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | B =>
    exact countSwap.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | CZ =>
    exact countS.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | KC =>
    exact countCX.independent rfl _ (by intro a; cases a <;> decide +kernel) (by decide +kernel)
  | I => exact absurd hρ (by decide)

end QCert.Minimality.QutritClifford
