/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real Clifford circuits: the presentation RCliff₂ (Figure 3)

Blake (FSCD 2026), Definition 16: the real Clifford fragment has the
generators `- : 0 → 0`, `H, Z : 1 → 1` and `CNOT : 2 → 2` (Table 1), the swap
being structural, and the ten rules of Figure 3.

Conventions as for Cliff₂ (`QCert.Minimality.Clifford`): wire `0` is the
bottom wire, the CNOT's control is wire `1`, rules are read left to right
with `seq`, and a gate drawn on non-adjacent wires, or a CNOT drawn upside
down, is conjugated by swaps (Figure 9).
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.RealClifford

open Circuit

/-- The gates of RCliff₂ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `-1`. -/
  | minus : Gate 0
  /-- Hadamard. -/
  | H : Gate 1
  /-- Pauli `Z`. -/
  | Z : Gate 1
  /-- The CNOT, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### Circuits on their own wires -/

abbrev H : Circuit Gate 1 := g1 .H
abbrev Z : Circuit Gate 1 := g1 .Z

/-- The scalar `-1` (on any number of wires). -/
abbrev minus {n : ℕ} : Circuit Gate n := g0 .minus

abbrev H₀ : Circuit Gate 2 := g1 .H
abbrev H₁ : Circuit Gate 2 := shift (g1 .H)
abbrev Z₀ : Circuit Gate 2 := g1 .Z
abbrev Z₁ : Circuit Gate 2 := shift (g1 .Z)
/-- The CNOT with control on the top wire `1` and target on wire `0`. -/
abbrev CX : Circuit Gate 2 := g2 .CX
/-- The swap. -/
abbrev σ : Circuit Gate 2 := g2 .swap
/-- The CNOT with control on the bottom wire `0` and target on wire `1`. -/
def XC : Circuit Gate 2 := seq [σ, CX, σ]

abbrev CX₀ : Circuit Gate 3 := g2 .CX
abbrev CX₁ : Circuit Gate 3 := shift (g2 .CX)
abbrev σ₀ : Circuit Gate 3 := g2 .swap
/-- The CNOT with control on wire `2` and target on wire `0` (Figure 9 (1)). -/
def CX₂₀ : Circuit Gate 3 := seq [σ₀, CX₁, σ₀]

/-! ### The rules of Figure 3 -/

/-- The rules of RCliff₂ (Figure 3). -/
inductive Ax
  /-- (−²): `(-1)^{⊗2} = id₀`. -/
  | minus2
  /-- (H²): `H H = id`. -/
  | H2
  /-- (Z²): `Z Z = id`. -/
  | Z2
  /-- (F): `Z H Z H = (-1) H Z H Z`. -/
  | F
  /-- (CX²): a CNOT twice is the identity. -/
  | CX2
  /-- (B): a CNOT followed by a reversed CNOT is a swap followed by a CNOT. -/
  | B
  /-- (ZC): `Z` on the target around a CNOT is the CNOT followed by `Z` on
  its control. -/
  | ZC
  /-- (CZr): `H ⊗ H` around a CNOT is the reversed CNOT. -/
  | CZr
  /-- (CF): `CNOT ; H₀ ; CNOT ; Z₀ ; H₀ = H₀ ; Z₀ ; CNOT ; H₀ ; CNOT`. -/
  | CF
  /-- (I): `CNOT₁₂ ; CNOT₀₁ ; CNOT₀₂ = CNOT₀₁ ; CNOT₁₂`, wires numbered
  from the top as in the figure (`CNOT_{cd}`: control `c`, target `d`). -/
  | I
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .minus2 => 0
  | .H2 | .Z2 | .F => 1
  | .CX2 | .B | .ZC | .CZr | .CF => 2
  | .I => 3

/-- The two sides of each rule of Figure 3, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .minus2 => (seq [minus, minus], 1)
  | .H2 => (seq [H, H], 1)
  | .Z2 => (seq [Z, Z], 1)
  | .F => (seq [Z, H, Z, H], seq [minus, H, Z, H, Z])
  | .CX2 => (seq [CX, CX], 1)
  | .B => (seq [CX, XC], seq [σ, CX])
  | .ZC => (seq [Z₀, CX, Z₀], seq [CX, Z₁])
  | .CZr => (seq [H₀, H₁, CX, H₀, H₁], XC)
  | .CF => (seq [CX, H₀, CX, Z₀, H₀], seq [H₀, Z₀, CX, H₀, CX])
  | .I => (seq [CX₀, CX₁, CX₂₀], seq [CX₁, CX₀])

/-- The presentation RCliff₂ of Figure 3. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.RealClifford
