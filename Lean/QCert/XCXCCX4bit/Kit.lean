/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The proof engine at {X, CX, CCX}: letters, and the rules as equations

Translation of `Kit.agda`: `Engine` instantiated at our gates.  The letters
are `Xₗ`, `CXₗ`, `CCXₗ` and `σₗ`, shifted by `Gen.up` (the Agda's `_↥`, so
`Xₗ ↥ ↥` is `Xₗ.up.up`).  Each rule of the theory and each swap rule is an
equation between letter lists on the bottom wires of a circuit of any width
(`Reasoning.ax_at`, `CircuitProp.pad`), and `liftE` moves it up.  A
derivation is `derive l r steps (by decide +kernel)`, its steps `perm ys`
(the same word up to letters on disjoint wires) and `rw i e` (rewrite at
position `i` by the equation `e`).

Names: the Agda's `r1⁼`, `σσ⁼`, `σX⁼`, … are `r1E`, `σσE`, `σXE`, …; `Eqn n`
is `Engine.Eqn SRel n`; `sym⁼`, `lift⁼`, `eqnʷ` are `symE`, `liftE`, `eqnW`.
The Agda's patterns `Xₗ` … are abbreviations here; to match on a letter,
use its constructors (`.gate1 (.gate .X_gate)`, `.gate2 .swap`, …).
-/
import QCert.XCXCCX4bit.Syntactics
import QCert.XCXCCX4bit.Lib.Reasoning
import QCert.XCXCCX4bit.Lib.Engine

namespace QCert.XCXCCX4bit

open QCert QCert.Circuit CircuitProp IndepProp Engine

/-- Equality of gates (the Agda's `gate-eq`). -/
def gateEq : {k : ℕ} → Gate k → Gate k → Bool
  | _, .X_gate, .X_gate => true
  | _, .CX_gate, .CX_gate => true
  | _, .CCX_gate, .CCX_gate => true

theorem gateEq_sound : ∀ {k : ℕ} (a b : Gate k), gateEq a b = true → a = b
  | _, .X_gate, .X_gate, _ => rfl
  | _, .CX_gate, .CX_gate, _ => rfl
  | _, .CCX_gate, .CCX_gate, _ => rfl

/-- The engine's parameters at our gates (the Agda's `gate-eq`, its
soundness, `code` and `one`). -/
instance : Engine.Gates Gate := ⟨gateEq, gateEq_sound, fun _ => 0, fun h => nomatch h⟩

/-- Equations of the theory, between letter lists on `n` wires. -/
abbrev Eqn (n : ℕ) : Type := Engine.Eqn SRel n

/-- Steps of a derivation on `n` wires. -/
abbrev Step (n : ℕ) : Type := Engine.Step SRel n

/-- The step `perm ys`. -/
abbrev perm {n : ℕ} (ys : List (Gn n)) : Step n := Engine.Step.perm ys

/-- The step `rw i e`. -/
abbrev rw {n : ℕ} (i : ℕ) (e : Eqn n) : Step n := Engine.Step.rw i e

export Reasoning (ax_at lift)

variable {n : ℕ}

/-! ## Letters -/

abbrev Xₗ : Gn (n + 1) := .gate1 (.gate .X_gate)
abbrev CXₗ : Gn (n + 2) := .gate2 (.gate .CX_gate)
abbrev CCXₗ : Gn (n + 3) := .gate3 (.gate .CCX_gate)
abbrev σₗ : Gn (n + 2) := .gate2 .swap

/-! ## The rules, on the bottom wires of a circuit of any width -/

def r1E : Eqn (n + 1) := eqnW [Xₗ, Xₗ] [] (ax_at SRel.r1 n) rfl rfl

def r2E : Eqn (n + 2) := eqnW [CXₗ, Xₗ.up, CXₗ, Xₗ.up] [Xₗ] (ax_at SRel.r2 n) rfl rfl

def r3E : Eqn (n + 2) := eqnW [CXₗ, σₗ, CXₗ, σₗ, CXₗ] [σₗ] (ax_at SRel.r3 n) rfl rfl

def r4E : Eqn (n + 3) := eqnW [CCXₗ, Xₗ.up.up, CCXₗ, Xₗ.up.up] [CXₗ] (ax_at SRel.r4 n) rfl rfl

def r5E : Eqn (n + 3) := eqnW [σₗ.up, CCXₗ, σₗ.up] [CCXₗ] (ax_at SRel.r5 n) rfl rfl

def r6E : Eqn (n + 3) :=
  eqnW [σₗ, CXₗ, σₗ, CCXₗ, σₗ, CXₗ, σₗ] [σₗ, CCXₗ, σₗ, CCXₗ, σₗ, CCXₗ, σₗ] (ax_at SRel.r6 n) rfl rfl

def r7E : Eqn (n + 4) :=
  eqnW [CCXₗ.up, CXₗ, CCXₗ.up] [σₗ, CCXₗ.up, σₗ, CXₗ] (ax_at SRel.r7 n) rfl rfl

/-! ## The swap rules -/

def σσE : Eqn (n + 2) := eqnW [σₗ, σₗ] [] (sym_rule Sym.σ_inv) rfl rfl

/-- A gate followed by the cycle `σ[ k ]` is the cycle followed by the gate
one wire up. -/
def σXE : Eqn (n + 2) :=
  eqnW [Xₗ, σₗ] [σₗ, Xₗ.up] (sym_rule (Sym.σ_nat₁ (PGate.gate Gate.X_gate))) rfl rfl

def σCXE : Eqn (n + 3) :=
  eqnW [CXₗ, σₗ.up, σₗ] [σₗ.up, σₗ, CXₗ.up] (sym_rule (Sym.σ_nat₂ (PGate.gate Gate.CX_gate))) rfl rfl

def σσσE : Eqn (n + 3) :=
  eqnW [σₗ, σₗ.up, σₗ] [σₗ.up, σₗ, σₗ.up] (sym_rule (Sym.σ_nat₂ PGate.swap)) rfl rfl

def σCCXE : Eqn (n + 4) :=
  eqnW [CCXₗ, σₗ.up.up, σₗ.up, σₗ] [σₗ.up.up, σₗ.up, σₗ, CCXₗ.up]
    (sym_rule (Sym.σ_nat₃ (PGate.gate Gate.CCX_gate))) rfl rfl

end QCert.XCXCCX4bit
