/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford+T circuits: the presentation CliffT₂ (Figure 5)

Blake (FSCD 2026), Definition 16: the Clifford+T fragment has the generators
`ω₈ : 0 → 0`, `H, T : 1 → 1` and `CNOT : 2 → 2` (Table 1), the swap being
structural, and the eleven rules of Figure 5.

Conventions as for Cliff₂ (`QCert.Minimality.Clifford`): wire `0` is the
bottom wire, the CNOT's control is wire `1`, rules are read left to right
with `seq`, and a gate drawn upside down is conjugated by the swap.  The
shortcuts of Figure 9 for `P_CliffT`: `S := T²`, `S† := S³`, `Z := S²`,
`X := H Z H`, `T† := T⁷`, the controlled Hadamard
`(CH) := S, H, T, CNOT, T†, H, S†` on the target, the Hadamard controlled
by `|0⟩` `(0CH) := CH` followed by `H` on the target, and the controlled
phase `(CS) := T ⊗ T, CNOT, T†` on the target, `CNOT`.
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.CliffordT

open Circuit

/-- The gates of CliffT₂ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `ω₈ = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- Hadamard. -/
  | H : Gate 1
  /-- The phase gate `T`. -/
  | T : Gate 1
  /-- The CNOT, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### One wire -/

/-- The scalar `ω₈` (on any number of wires). -/
abbrev ω {n : ℕ} : Circuit Gate n := g0 .ω

abbrev H : Circuit Gate 1 := g1 .H
abbrev T : Circuit Gate 1 := g1 .T
/-- `S := T²`. -/
def S : Circuit Gate 1 := seq [T, T]
/-- `Z := S²`. -/
def Z : Circuit Gate 1 := seq [S, S]
/-- `X := H Z H`. -/
def X : Circuit Gate 1 := seq [H, Z, H]
/-- `T† := T⁷`. -/
def Tdg : Circuit Gate 1 := seq (List.replicate 7 T)

/-! ### Two wires -/

abbrev H₀ : Circuit Gate 2 := g1 .H
abbrev T₀ : Circuit Gate 2 := g1 .T
abbrev T₁ : Circuit Gate 2 := shift (g1 .T)
/-- `S := T²` on wire `0`. -/
def S₀ : Circuit Gate 2 := seq [T₀, T₀]
/-- `S := T²` on wire `1`. -/
def S₁ : Circuit Gate 2 := seq [T₁, T₁]
/-- `S† := S³` on wire `0`. -/
def Sdg₀ : Circuit Gate 2 := seq [S₀, S₀, S₀]
/-- `T† := T⁷` on wire `0`. -/
def Tdg₀ : Circuit Gate 2 := seq (List.replicate 7 T₀)
abbrev CX : Circuit Gate 2 := g2 .CX
abbrev σ : Circuit Gate 2 := g2 .swap
/-- The CNOT with control on wire `0` and target on wire `1`. -/
def revCX : Circuit Gate 2 := seq [σ, CX, σ]
/-- (CS): the controlled `S`, control on wire `1`. -/
def CS : Circuit Gate 2 := seq [T₁, T₀, CX, Tdg₀, CX]
/-- (CH): the controlled Hadamard, control on wire `1`, target on wire `0`. -/
def CH : Circuit Gate 2 := seq [S₀, H₀, T₀, CX, Tdg₀, H₀, Sdg₀]
/-- (0CH): the Hadamard on wire `0` controlled by `|0⟩` on wire `1`. -/
def oCH : Circuit Gate 2 := seq [CH, H₀]
/-- The controlled Hadamard drawn upside down: control on wire `0`. -/
def CHr : Circuit Gate 2 := seq [σ, CH, σ]
/-- (0CH) drawn upside down: control `|0⟩` on wire `0`. -/
def oCHr : Circuit Gate 2 := seq [σ, oCH, σ]

/-! ### The rules of Figure 5 -/

/-- The rules of CliffT₂ (Figure 5). -/
inductive Ax
  /-- (ω⁸): `ω₈^{⊗8} = id₀`. -/
  | ω8
  /-- (T⁸): `T⁸ = id`. -/
  | T8
  /-- (H²): `H H = id`. -/
  | H2
  /-- (E): `H S H = ω₈ S S S H S S S`. -/
  | E
  /-- (TX): `ω₈ T† X = X T`. -/
  | TX
  /-- (CPh): a CNOT, `T` on its control, a CNOT, is `T` on the top wire. -/
  | CPh
  /-- (B): a CNOT followed by a reversed CNOT is a swap followed by a CNOT. -/
  | B
  /-- (CZ): `H` on the target around a CNOT is
  `(S ⊗ S) CNOT (id ⊗ S S S) CNOT`. -/
  | CZ
  /-- (CSH): the controlled `S` and the Hadamard controlled by `|0⟩` commute. -/
  | CSH
  /-- (HT²): `CH ; T ; 0CH ; T† = T ; 0CH ; T† ; CH` on the target. -/
  | HT2
  /-- (HTH): `0CH ; T ; CH` on the bottom wire followed by its mirror image on
  the top wire (controlled from the bottom) equals the mirror image followed
  by the original. -/
  | HTH
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .ω8 => 0
  | .T8 | .H2 | .E | .TX => 1
  | .CPh | .B | .CZ | .CSH | .HT2 | .HTH => 2

/-- The two sides of each rule of Figure 5, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .ω8 => (seq (List.replicate 8 ω), 1)
  | .T8 => (seq (List.replicate 8 T), 1)
  | .H2 => (seq [H, H], 1)
  | .E => (seq [H, S, H], seq [ω, S, S, S, H, S, S, S])
  | .TX => (seq [ω, Tdg, X], seq [X, T])
  | .CPh => (seq [CX, T₁, CX], T₁)
  | .B => (seq [CX, revCX], seq [σ, CX])
  | .CZ => (seq [H₀, CX, H₀], seq [S₁, S₀, CX, S₀, S₀, S₀, CX])
  | .CSH => (seq [CS, oCH], seq [oCH, CS])
  | .HT2 => (seq [CH, T₀, oCH, Tdg₀], seq [T₀, oCH, Tdg₀, CH])
  | .HTH => (seq [oCH, T₀, CH, oCHr, T₁, CHr], seq [oCHr, T₁, CHr, oCH, T₀, CH])

/-- The presentation CliffT₂ of Figure 5. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.CliffordT
