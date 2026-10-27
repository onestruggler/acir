/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of RCliff₂ (Theorem 37 (2), Figure 8 (b))

Each rule of Figure 3 is independent of the others, by the separator of
Figure 8 (b): weighted counts, and for (CF) and (CZr) the projective
substitutions `[Z := id]∼` and `[H := id]∼` (Definition 34), realised as
matrices over ℚ(ω) modulo units: the integer matrices over ℤ[ω] (the
Hadamard scaled by `√2`, a unit of ℚ(ω), which does not change the
projective class) with the substituted gate replaced.
-/
import QCert.Minimality.RealClifford.Semantics
import QCert.Minimality.Models

namespace QCert.Minimality.RealClifford

open Qubit

/-- `?-`. -/
def hasMinus : Weights Gate Occ := ⟨fun _ => Occ.yes, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `?H`. -/
def hasH : Weights Gate Occ := ⟨fun _ => 0, fun | .H => Occ.yes | .Z => 0, fun _ => 0, fun _ => 0⟩
/-- `?Z`. -/
def hasZ : Weights Gate Occ := ⟨fun _ => 0, fun | .Z => Occ.yes | .H => 0, fun _ => 0, fun _ => 0⟩
/-- `#{-}_[2]`. -/
def countMinus : Weights Gate (ZMod 2) := ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `?CNOT`. -/
def hasCX : Weights Gate Occ :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => Occ.yes | .swap => 0, fun _ => 0⟩
/-- `#{SWAP}_[2]`. -/
def countSwap : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 0, fun | .CX => 0 | .swap => 1, fun _ => 0⟩
/-- `#{Z}_[2]`. -/
def countZ : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun | .Z => 1 | .H => 0, fun _ => 0, fun _ => 0⟩
/-- `arg det₂` in units of `π/4`: `det ⟦-⟧ = -1` weighs `4 · 4 = 0`,
`det ⟦H⟧ = det ⟦Z⟧ = -1` weigh `2 · 4 = 0`, `det ⟦CNOT⟧ = -1` weighs `4`, and
the swap `ε₂ = π`. -/
def argdet2 : Weights Gate (ZMod 8) :=
  ⟨fun _ => 0, fun _ => 0, fun | .CX => 4 | .swap => 4, fun _ => 0⟩

/-- The identity matrix on one wire. -/
def idZ : Op ZOmega 2 1 := fun s t => if s 0 = t 0 then 1 else 0

/-- `[Z := id]∼`: the gates over ℤ[ω] with `Z` interpreted as the identity. -/
def substZ : ScaledOps Gate ZOmega 2 where
  ops := { ops with gate1 := fun | .H => hadZ | .Z => idZ }
  e1
    | .H => 1
    | .Z => 0
  e2 _ := 0
  e3 g := nomatch g

/-- `[H := id]∼`: the gates over ℤ[ω] with `H` interpreted as the identity. -/
def substH : ScaledOps Gate ZOmega 2 where
  ops := { ops with gate1 := fun | .H => idZ | .Z => zZ }
  e1 _ := 0
  e2 _ := 0
  e3 g := nomatch g

theorem substZ_sym {k : ℕ} {w v : Circuit Gate k} :
    Sym pres.swap k w v → substZ.ops.eval k w = substZ.ops.eval k v
  | .invol => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .H => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .Z => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .CX => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .swap => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat3 g => nomatch g

theorem substH_sym {k : ℕ} {w v : Circuit Gate k} :
    Sym pres.swap k w v → substH.ops.eval k w = substH.ops.eval k v
  | .invol => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .H => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .Z => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .CX => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .swap => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat3 g => nomatch g

theorem independent_CF : pres.Independent .CF :=
  independent_of_proj ZOmega.toQ ZOmega.toQ_injective substZ.ops substZ_sym .CF
    (fun a ha hne => by
      cases a
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ (-1) isUnit_toQ_neg_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substZ 1 isUnit_toQ_one (by decide +kernel)
      · exact absurd rfl hne
      · exact absurd ha (by decide))
    ⟨![0, 0], ![0, 0], ![0, 1], ![1, 1], by
      simp only [eval_apply_eq substZ.ops]; decide +kernel⟩

theorem independent_CZr : pres.Independent .CZr :=
  independent_of_proj ZOmega.toQ ZOmega.toQ_injective substH.ops substH_sym .CZr
    (fun a ha hne => by
      cases a
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substH (-1) isUnit_toQ_neg_one (by decide +kernel)
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact absurd rfl hne
      · exact projHyp substH 1 isUnit_toQ_one (by decide +kernel)
      · exact absurd ha (by decide))
    ⟨![0, 0], ![0, 0], ![1, 0], ![1, 0], by
      simp only [eval_apply_eq substH.ops]; decide +kernel⟩

/-- Theorem 37 (2): RCliff₂ is minimal (in all arities). -/
theorem minimal : pres.Minimal
  | .minus2 => hasMinus.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .H2 => hasH.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .Z2 => hasZ.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .F => countMinus.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .CX2 => hasCX.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .B => countSwap.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .ZC => countZ.independent rfl _ (by intro a; cases a <;> decide) (by decide)
  | .CF => independent_CF
  | .CZr => independent_CZr
  | .I => argdet2.independent rfl _ (by intro a; cases a <;> decide) (by decide)

end QCert.Minimality.RealClifford
