/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qutrit Clifford circuits: the presentation Cliff₃ (Figure 4)

Blake (FSCD 2026), Definition 17: the qutrit Clifford fragment has the
generators `ω₁₂ : 0 → 0`, `H, S : 1 → 1` and `CNOT : 2 → 2` (Table 1), the
swap being structural, and the ten rules of Figure 4.

Conventions as for Cliff₂ (`QCert.Minimality.Clifford`): wire `0` is the
bottom wire, the CNOT's control is wire `1`, rules are read left to right
with `seq`, and gates drawn on non-adjacent wires or upside down are
conjugated by swaps.  The shortcuts of Figure 9 for `P_Cliff3`: `K := H²`,
`H† := H³`, `S† := S²`, `S' := H² S H²`, `Z := S² S'`, `X := H Z H³`.

Correction: Figure 4 prints the scalar of (E) as `ω₁₂⁷`; with the semantics
of Definition 17 the two sides then differ by the factor `-1`
(`QCert.Minimality.QutritClifford.E_printed_unsound`), and the rule holds with
`ω₁₂`.  `Ax.E` is the corrected rule.
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.QutritClifford

open Circuit

/-- The gates of Cliff₃ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `ω₁₂ = e^{iπ/6}`. -/
  | ω : Gate 0
  /-- The qutrit Hadamard. -/
  | H : Gate 1
  /-- The qutrit phase gate `S`. -/
  | S : Gate 1
  /-- The qutrit CNOT, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### One wire -/

/-- The scalar `ω₁₂` (on any number of wires). -/
abbrev ω {n : ℕ} : Circuit Gate n := g0 .ω

abbrev H : Circuit Gate 1 := g1 .H
abbrev S : Circuit Gate 1 := g1 .S
/-- `K := H²`. -/
def K : Circuit Gate 1 := seq [H, H]
/-- `S' := H² S H²`. -/
def S' : Circuit Gate 1 := seq [H, H, S, H, H]
/-- `Z := S² S'`. -/
def Z : Circuit Gate 1 := seq [S, S, S']
/-- `X := H Z H³`. -/
def X : Circuit Gate 1 := seq [H, Z, H, H, H]

/-! ### Two wires -/

abbrev H₀ : Circuit Gate 2 := g1 .H
abbrev S₀ : Circuit Gate 2 := g1 .S
abbrev S₁ : Circuit Gate 2 := shift (g1 .S)
/-- `K := H²` on wire `0`. -/
def K₀ : Circuit Gate 2 := seq [H₀, H₀]
/-- `K := H²` on wire `1`. -/
def K₁ : Circuit Gate 2 := seq [shift (g1 .H), shift (g1 .H)]
abbrev CX : Circuit Gate 2 := g2 .CX
abbrev σ : Circuit Gate 2 := g2 .swap
/-- The CNOT with control on wire `0` and target on wire `1`. -/
def revCX : Circuit Gate 2 := seq [σ, CX, σ]

/-! ### Three wires -/

abbrev CX₀ : Circuit Gate 3 := g2 .CX
abbrev CX₁ : Circuit Gate 3 := shift (g2 .CX)
abbrev σ₀ : Circuit Gate 3 := g2 .swap
/-- The CNOT with control on wire `2` and target on wire `0` (Figure 9 (1)). -/
def CX₂₀ : Circuit Gate 3 := seq [σ₀, CX₁, σ₀]

/-! ### The rules of Figure 4 -/

/-- The rules of Cliff₃ (Figure 4). -/
inductive Ax
  /-- (ω¹²): `ω₁₂^{⊗12} = id₀`. -/
  | ω12
  /-- (H⁴): `H⁴ = id`. -/
  | H4
  /-- (S³): `S³ = id`. -/
  | S3
  /-- (E), corrected: `S H S = H H H S S H H H ω₁₂` (Figure 4 prints `ω₁₂⁷`). -/
  | E
  /-- (SS'): `S K S K = K S K S`. -/
  | SS'
  /-- (CPh): a CNOT, `S` on its control and `K` on its target, a CNOT, is
  `S ⊗ K`. -/
  | CPh
  /-- (KC): `K` on the control followed by a CNOT is two CNOTs followed by
  `K` on the control. -/
  | KC
  /-- (CZ): `H ; CNOT ; H H H` on the target is
  `(S ⊗ S) CNOT (id ⊗ S S) CNOT CNOT`. -/
  | CZ
  /-- (B): the swap followed by a CNOT is a CNOT, two reversed CNOTs and `K`
  on the top wire. -/
  | B
  /-- (I): `CNOT₁₂ ; CNOT₀₁ ; CNOT₀₂ = CNOT₀₁ ; CNOT₁₂`, wires numbered
  from the top as in the figure (`CNOT_{cd}`: control `c`, target `d`). -/
  | I
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .ω12 => 0
  | .H4 | .S3 | .E | .SS' => 1
  | .CPh | .KC | .CZ | .B => 2
  | .I => 3

/-- The two sides of each rule of Figure 4, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .ω12 => (seq (List.replicate 12 ω), 1)
  | .H4 => (seq [H, H, H, H], 1)
  | .S3 => (seq [S, S, S], 1)
  | .E => (seq [S, H, S], seq [H, H, H, S, S, H, H, H, ω])
  | .SS' => (seq [S, K, S, K], seq [K, S, K, S])
  | .CPh => (seq [CX, S₁, K₀, CX], seq [S₁, K₀])
  | .KC => (seq [K₁, CX], seq [CX, CX, K₁])
  | .CZ => (seq [H₀, CX, H₀, H₀, H₀], seq [S₁, S₀, CX, S₀, S₀, CX, CX])
  | .B => (seq [σ, CX], seq [CX, revCX, revCX, K₁])
  | .I => (seq [CX₀, CX₁, CX₂₀], seq [CX₁, CX₀])

/-- The right-hand side of (E) as printed in Figure 4, with `ω₁₂⁷`. -/
def E_printed_rhs : Circuit Gate 1 := seq [H, H, H, S, S, H, H, H, seq (List.replicate 7 ω)]

/-- The presentation Cliff₃ of Figure 4, with (E) corrected. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.QutritClifford
