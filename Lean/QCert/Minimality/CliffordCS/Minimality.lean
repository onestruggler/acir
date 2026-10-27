/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Minimality of CliffCS₂ (Theorem 37 (5), Figure 8 (e))

The rules of Figure 6 on at most two wires are independent of the others, by
the separators of Figure 8 (e): weighted counts, and for (CSr) and (CE) the
projective substitutions `[CS := CS·Z₀]∼` and `[CS := CS·Z₀Z₁]∼`
(Definition 34; the gates drawn `CSz`, `CSzz`: `CS` followed by `Z` on the
bottom wire, resp. on both wires), realised as matrices over ℚ(ω) modulo
units.  The three-wire rule (I) is independent too, by `arg det₂`.  Figure
8 (e) gives no separator for (SH_k).
-/
import QCert.Minimality.CliffordCS.Semantics
import QCert.Minimality.Models

namespace QCert.Minimality.CliffordCS

open Qubit

/-- `?ω₈`. -/
def hasω : Weights Gate Occ := ⟨fun _ => Occ.yes, fun _ => 0, fun _ => 0, fun _ => 0⟩
/-- `?H`. -/
def hasH : Weights Gate Occ := ⟨fun _ => 0, fun | .H => Occ.yes | .S => 0, fun _ => 0, fun _ => 0⟩
/-- `?S`. -/
def hasS : Weights Gate Occ := ⟨fun _ => 0, fun | .S => Occ.yes | .H => 0, fun _ => 0, fun _ => 0⟩
/-- `#{H}_[2]`. -/
def countH : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun | .H => 1 | .S => 0, fun _ => 0, fun _ => 0⟩
/-- `?CS`. -/
def hasCS : Weights Gate Occ :=
  ⟨fun _ => 0, fun _ => 0, fun | .CS => Occ.yes | .swap => 0, fun _ => 0⟩
/-- `#{SWAP}_[2]`. -/
def countSwap : Weights Gate (ZMod 2) :=
  ⟨fun _ => 0, fun _ => 0, fun | .CS => 0 | .swap => 1, fun _ => 0⟩
/-- `#{S, H}_[2]`. -/
def countSH : Weights Gate (ZMod 2) := ⟨fun _ => 0, fun _ => 1, fun _ => 0, fun _ => 0⟩
/-- `arg det₂` in units of `π/4`: `det ⟦ω₈⟧ = e^{iπ/4}` weighs `4`,
`det ⟦H⟧ = -1` weighs `2 · 4 = 0`, `det ⟦S⟧ = i` weighs `2 · 2 = 4`,
`det ⟦CS⟧ = i` weighs `2`, and the swap `ε₂ = π`. -/
def argdet2 : Weights Gate (ZMod 8) :=
  ⟨fun _ => 4, fun | .H => 0 | .S => 4, fun | .CS => 2 | .swap => 4, fun _ => 0⟩

/-- The matrix of `CS` followed by `Z` on wire `0`: `i^{xy} (-1)^y`. -/
def csz : Op ZOmega 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then ZOmega.I ^ ((s 0 : ℕ) * (s 1 : ℕ)) * (-1) ^ (s 0 : ℕ) else 0

/-- The matrix of `CS` followed by `Z` on both wires: `i^{xy} (-1)^{x + y}`. -/
def cszz : Op ZOmega 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then
    ZOmega.I ^ ((s 0 : ℕ) * (s 1 : ℕ)) * (-1) ^ ((s 0 : ℕ) + (s 1 : ℕ)) else 0

/-- `csz` is the matrix of the circuit `CS ; Z₀` (`Z := S²`). -/
theorem csz_eq : csz = ops.eval 2 (seq [CS, S₀, S₀]) :=
  eq_eval_of_matRows ops _ _ (by decide +kernel)

/-- `cszz` is the matrix of the circuit `CS ; Z₀ ; Z₁`. -/
theorem cszz_eq : cszz = ops.eval 2 (seq [CS, S₀, S₀, S₁, S₁]) :=
  eq_eval_of_matRows ops _ _ (by decide +kernel)

/-- `[CS := CS·Z₀]∼`. -/
def substCSz : ScaledOps Gate ZOmega 2 where
  ops := { ops with gate2 := fun | .CS => csz | .swap => swapZ }
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

/-- `[CS := CS·Z₀Z₁]∼`. -/
def substCSzz : ScaledOps Gate ZOmega 2 where
  ops := { ops with gate2 := fun | .CS => cszz | .swap => swapZ }
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

theorem substCSz_sym {k : ℕ} {w v : Circuit Gate k} :
    Sym pres.swap k w v → substCSz.ops.eval k w = substCSz.ops.eval k v
  | .invol => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .H => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .S => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .CS => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .swap => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat3 g => nomatch g

theorem substCSzz_sym {k : ℕ} {w v : Circuit Gate k} :
    Sym pres.swap k w v → substCSzz.ops.eval k w = substCSzz.ops.eval k v
  | .invol => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .H => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat1 .S => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .CS => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat2 .swap => eval_eq_of_evalRows _ (by decide +kernel)
  | .nat3 g => nomatch g

theorem independent_CSr : pres.Independent .CSr :=
  independent_of_proj ZOmega.toQ ZOmega.toQ_injective substCSz.ops substCSz_sym .CSr
    (fun a ha hne => by
      cases a with
      | CSr => exact absurd rfl hne
      | I => exact absurd ha (by decide)
      | SH k => exact absurd ha (by simp [pres, Ax.arity])
      | _ => exact projHyp substCSz 1 isUnit_toQ_one (by decide +kernel))
    ⟨![0, 0], ![0, 0], ![1, 0], ![1, 0], by
      simp only [eval_apply_eq substCSz.ops]; decide +kernel⟩

theorem independent_CE : pres.Independent .CE :=
  independent_of_proj ZOmega.toQ ZOmega.toQ_injective substCSzz.ops substCSzz_sym .CE
    (fun a ha hne => by
      cases a with
      | CE => exact absurd rfl hne
      | I => exact absurd ha (by decide)
      | SH k => exact absurd ha (by simp [pres, Ax.arity])
      | XCS => exact projHyp substCSzz (-1) isUnit_toQ_neg_one (by decide +kernel)
      | _ => exact projHyp substCSzz 1 isUnit_toQ_one (by decide +kernel))
    ⟨![0, 0], ![0, 1], ![1, 0], ![1, 0], by
      simp only [eval_apply_eq substCSzz.ops]; decide +kernel⟩

/-- Theorem 37 (5): CliffCS₂ is minimal up to two wires. -/
theorem minimalUpTo_two : pres.MinimalUpTo 2 := by
  rw [PropPresentation.minimalUpTo_iff]
  intro ρ hρ
  cases ρ with
  | ω8 => exact hasω.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide) (by decide)
  | H2 => exact hasH.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide) (by decide)
  | S4 => exact hasS.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide) (by decide)
  | E => exact countH.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide) (by decide)
  | CPh => exact hasCS.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide +kernel) (by decide +kernel)
  | B => exact countSwap.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide +kernel) (by decide +kernel)
  | XCS => exact countSH.independent rfl _ (by
      intro a; cases a with | SH k => intro h; exact absurd h (by simp [pres, Ax.arity])
                            | _ => decide +kernel) (by decide +kernel)
  | CSr => exact independent_CSr
  | CE => exact independent_CE
  | I => exact absurd hρ (by decide)
  | SH k => exact absurd hρ (by simp [pres, Ax.arity])

/-- Theorem 37, beyond the bound: the three-wire rule (I) is independent. -/
theorem independent_I : pres.Independent .I :=
  argdet2.independent rfl _ (by
    intro a; cases a with | SH k => fin_cases k <;> decide +kernel | _ => decide +kernel)
    (by decide +kernel)

end QCert.Minimality.CliffordCS
