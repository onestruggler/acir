/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qubit Clifford circuits: the presentation Cliff₂ (Figure 2)

Blake (FSCD 2026), Definition 16: the qubit Clifford fragment has the
generators `ω₈ : 0 → 0`, `H, S : 1 → 1` and `CNOT : 2 → 2` (Table 1), the swap
being structural, and the eight rules of Figure 2.

Conventions.  Wire `0` is the bottom wire of a diagram (the last tensor
factor); a two-wire gate sits on wires `0, 1` and the CNOT's control is the
top wire `1`, its target wire `0`, as drawn in Figure 2.  Rules are written
in the diagrams' left-to-right order with `seq` (`seq [c₁, …, cₖ]` applies
`c₁` first).  A gate drawn on non-adjacent wires is the PROP's shortcut,
conjugation by swaps (Figure 9, (1) and (2)), and a CNOT drawn with its
control below its target is the CNOT conjugated by the swap.
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.Clifford

open Circuit

/-- The gates of Cliff₂ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `ω₈ = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- Hadamard. -/
  | H : Gate 1
  /-- The phase gate `S`. -/
  | S : Gate 1
  /-- The CNOT, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### Circuits on their own wires -/

/-- One-wire circuits. -/
abbrev H : Circuit Gate 1 := g1 .H
abbrev S : Circuit Gate 1 := g1 .S

/-- The scalar `ω₈` (on any number of wires). -/
abbrev ω {n : ℕ} : Circuit Gate n := g0 .ω

/-- Two-wire circuits: `H₀` on wire `0`, `S₁` on wire `1`, … -/
abbrev H₀ : Circuit Gate 2 := g1 .H
abbrev H₁ : Circuit Gate 2 := shift (g1 .H)
abbrev S₀ : Circuit Gate 2 := g1 .S
abbrev S₁ : Circuit Gate 2 := shift (g1 .S)
/-- The CNOT with control on the top wire `1` and target on wire `0`. -/
abbrev CX : Circuit Gate 2 := g2 .CX
/-- The swap. -/
abbrev σ : Circuit Gate 2 := g2 .swap
/-- The CNOT with control on the bottom wire `0` and target on wire `1`. -/
def XC : Circuit Gate 2 := seq [σ, CX, σ]

/-- Three-wire circuits: `CX₀` on wires `0, 1`, `CX₁` on wires `1, 2`. -/
abbrev CX₀ : Circuit Gate 3 := g2 .CX
abbrev CX₁ : Circuit Gate 3 := shift (g2 .CX)
abbrev σ₀ : Circuit Gate 3 := g2 .swap
/-- The CNOT with control on the top wire `2` and target on the bottom wire
`0`, crossing wire `1`: Figure 9, shortcut (1). -/
def CX₂₀ : Circuit Gate 3 := seq [σ₀, CX₁, σ₀]

/-! ### The rules of Figure 2 -/

/-- The rules of Cliff₂ (Figure 2). -/
inductive Ax
  /-- (ω⁸): `ω₈^{⊗8} = id₀`. -/
  | ω8
  /-- (H²): `H H = id`. -/
  | H2
  /-- (S⁴): `S S S S = id`. -/
  | S4
  /-- (E): `H S H = ω₈ S S S H S S S`. -/
  | E
  /-- (CPh): a CNOT, `S` on its control, a CNOT, is `S` on the top wire. -/
  | CPh
  /-- (B): a CNOT followed by a reversed CNOT is a swap followed by a CNOT. -/
  | B
  /-- (CZ): `H` on the target around a CNOT is
  `(S ⊗ S) CNOT (id ⊗ S S S) CNOT`. -/
  | CZ
  /-- (I): `CNOT₁₂ ; CNOT₀₁ ; CNOT₀₂ = CNOT₀₁ ; CNOT₁₂` on three wires
  (wires counted from the top in the label). -/
  | I
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .ω8 => 0
  | .H2 | .S4 | .E => 1
  | .CPh | .B | .CZ => 2
  | .I => 3

/-- The two sides of each rule of Figure 2, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .ω8 => (seq (List.replicate 8 ω), 1)
  | .H2 => (seq [H, H], 1)
  | .S4 => (seq [S, S, S, S], 1)
  | .E => (seq [H, S, H], seq [ω, S, S, S, H, S, S, S])
  | .CPh => (seq [CX, S₁, CX], S₁)
  | .B => (seq [CX, XC], seq [σ, CX])
  | .CZ => (seq [H₀, CX, H₀], seq [S₁, S₀, CX, S₀, S₀, S₀, CX])
  | .I => (seq [CX₀, CX₁, CX₂₀], seq [CX₁, CX₀])

/-- The presentation Cliff₂ of Figure 2. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.Clifford
