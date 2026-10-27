/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford+CS circuits: the presentation CliffCS₂ (Figure 6)

Blake (FSCD 2026), Definition 16: the Clifford+CS fragment has the
generators `ω₈ : 0 → 0`, `H, S : 1 → 1` and `CS : 2 → 2` (Table 1), the swap
being structural, and the fourteen rules of Figure 6 ((SH_k) counting for
`k ∈ {0, 1, 2, 3}`).

Conventions as for Cliff₂ (`QCert.Minimality.Clifford`): wire `0` is the
bottom wire, rules are read left to right with `seq`, and a gate drawn on
non-adjacent wires or upside down is conjugated by swaps.  `CS` is the
controlled-`S` gate, symmetric in its two wires (drawn with a dashed
line).  The shortcuts of Figure 9 for `P_CliffCS`: `Z := S²`, `X := H Z H`,
`S† := S³`, and the CNOT `(CX) := H, CS, CS, H` on the target (wire `0`).
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.CliffordCS

open Circuit

/-- The gates of CliffCS₂ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `ω₈ = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- Hadamard. -/
  | H : Gate 1
  /-- The phase gate `S`. -/
  | S : Gate 1
  /-- The controlled-`S` gate. -/
  | CS : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### One and two wires -/

/-- The scalar `ω₈` (on any number of wires). -/
abbrev ω {n : ℕ} : Circuit Gate n := g0 .ω

abbrev H : Circuit Gate 1 := g1 .H
abbrev S : Circuit Gate 1 := g1 .S

abbrev H₀ : Circuit Gate 2 := g1 .H
abbrev H₁ : Circuit Gate 2 := shift (g1 .H)
abbrev S₀ : Circuit Gate 2 := g1 .S
abbrev S₁ : Circuit Gate 2 := shift (g1 .S)
abbrev CS : Circuit Gate 2 := g2 .CS
abbrev σ : Circuit Gate 2 := g2 .swap
/-- (CX): the CNOT, control on wire `1`, target on wire `0`. -/
def CX : Circuit Gate 2 := seq [H₀, CS, CS, H₀]
/-- The CNOT with control on wire `0` and target on wire `1`. -/
def revCX : Circuit Gate 2 := seq [σ, CX, σ]

/-! ### Three wires -/

namespace W3

abbrev H₀ : Circuit Gate 3 := g1 .H
abbrev H₁ : Circuit Gate 3 := shift (g1 .H)
/-- `CS` on wires `0, 1`. -/
abbrev CS₀ : Circuit Gate 3 := g2 .CS
/-- `CS` on wires `1, 2`. -/
abbrev CS₁ : Circuit Gate 3 := shift (g2 .CS)
abbrev σ₀ : Circuit Gate 3 := g2 .swap
/-- (CX) on wires `1` (control), `0` (target). -/
def CX₀ : Circuit Gate 3 := seq [H₀, CS₀, CS₀, H₀]
/-- (CX) on wires `2` (control), `1` (target). -/
def CX₁ : Circuit Gate 3 := seq [H₁, CS₁, CS₁, H₁]
/-- (CX) from wire `2` to wire `0` (Figure 9 (1)). -/
def CX₂₀ : Circuit Gate 3 := seq [σ₀, CX₁, σ₀]

end W3

/-! ### The rules of Figure 6 -/

/-- The rules of CliffCS₂ (Figure 6). -/
inductive Ax
  /-- (ω⁸): `ω₈^{⊗8} = id₀`. -/
  | ω8
  /-- (H²): `H H = id`. -/
  | H2
  /-- (S⁴): `S S S S = id`. -/
  | S4
  /-- (E): `H S H = ω₈ S S S H S S S`. -/
  | E
  /-- (CPh): `CS ; S` on the top wire `; CS CS CS` is `S` on the top wire. -/
  | CPh
  /-- (CSr): `CS` is `CS` conjugated by the swap. -/
  | CSr
  /-- (B): a CNOT followed by a reversed CNOT is a swap followed by a CNOT. -/
  | B
  /-- (XCS): `X = H S S H` on the top wire followed by `CS` is
  `CS CS CS` followed by `X` on the top wire and `S` on the bottom wire. -/
  | XCS
  /-- (CE): `S H CS H CS = CS H CS H S`, `S` and `H` on the top wire. -/
  | CE
  /-- (I): `CNOT₁₂ ; CNOT₀₁ ; CNOT₀₂ = CNOT₀₁ ; CNOT₁₂`, wires numbered
  from the top as in the figure (`CNOT_{cd}`: control `c`, target `d`). -/
  | I
  /-- (SH_k), `k ∈ {0, 1, 2, 3}`: on three wires, the dashed box repeating
  its `CS` gate `k` times. -/
  | SH (k : Fin 4)
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .ω8 => 0
  | .H2 | .S4 | .E => 1
  | .CPh | .CSr | .B | .XCS | .CE => 2
  | .I | .SH _ => 3

/-- The two sides of each rule of Figure 6, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .ω8 => (seq (List.replicate 8 ω), 1)
  | .H2 => (seq [H, H], 1)
  | .S4 => (seq [S, S, S, S], 1)
  | .E => (seq [H, S, H], seq [ω, S, S, S, H, S, S, S])
  | .CPh => (seq [CS, S₁, CS, CS, CS], S₁)
  | .CSr => (CS, seq [σ, CS, σ])
  | .B => (seq [CX, revCX], seq [σ, CX])
  | .XCS => (seq [H₁, S₁, S₁, H₁, CS], seq [CS, CS, CS, H₁, S₁, S₁, H₁, S₀])
  | .CE => (seq [S₁, H₁, CS, H₁, CS], seq [CS, H₁, CS, H₁, S₁])
  | .I => (seq [W3.CX₀, W3.CX₁, W3.CX₂₀], seq [W3.CX₁, W3.CX₀])
  | .SH k =>
    (seq [W3.CS₀, W3.H₁, seq (List.replicate k W3.CS₀), W3.H₁, W3.CS₁, W3.H₁,
        seq (List.replicate k W3.CS₁)],
     seq [W3.CS₁, W3.H₁, seq (List.replicate k W3.CS₁), W3.H₁, W3.CS₀, W3.H₁,
        seq (List.replicate k W3.CS₀)])

/-- The presentation CliffCS₂ of Figure 6. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.CliffordCS
