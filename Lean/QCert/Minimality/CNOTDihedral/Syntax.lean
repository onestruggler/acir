/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: the presentation CNOTdihe₂ (Figure 7)

Blake (FSCD 2026), Definition 16: the CNOT-dihedral fragment has the
generators `ω₈ : 0 → 0`, `X, T : 1 → 1` and `CNOT : 2 → 2` (Table 1), the
swap being structural, and the eleven rules of Figure 7.

Conventions as for Cliff₂ (`QCert.Minimality.Clifford`): wire `0` is the
bottom wire, the CNOT's control is wire `1`, rules are read left to right
with `seq`, and gates drawn on non-adjacent wires are conjugated by swaps
(Figure 9).  The shortcuts of Figure 9: `Z := S²`, `S := T²`, `T† := T⁷`
(the shortcut (T†) of the Clifford+T fragment, which Figure 7 uses), the
two-wire phase gadget `(CT)` (blue squares: CNOT, `T` on the target, CNOT)
and the three-wire one `(CCT)` (green squares).
-/
import QCert.Minimality.Basic

namespace QCert.Minimality.CNOTDihedral

open Circuit

/-- The gates of CNOTdihe₂ (Table 1) and the structural swap. -/
inductive Gate : ℕ → Type
  /-- The scalar `ω₈ = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- Pauli `X`. -/
  | X : Gate 1
  /-- The phase gate `T`. -/
  | T : Gate 1
  /-- The CNOT, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The structural swap `σ`. -/
  | swap : Gate 2
  deriving DecidableEq

/-! ### Circuits on their own wires -/

/-- The scalar `ω₈` (on any number of wires). -/
abbrev ω {n : ℕ} : Circuit Gate n := g0 .ω

abbrev X : Circuit Gate 1 := g1 .X
abbrev T : Circuit Gate 1 := g1 .T
/-- `T† := T⁷` (Figure 9, (T†)). -/
def Tdg : Circuit Gate 1 := seq (List.replicate 7 T)

abbrev X₀ : Circuit Gate 2 := g1 .X
abbrev X₁ : Circuit Gate 2 := shift (g1 .X)
abbrev T₀ : Circuit Gate 2 := g1 .T
abbrev T₁ : Circuit Gate 2 := shift (g1 .T)
/-- `Z := S² = T⁴` (Figure 9, (Z) and (S)) on wire `0`. -/
def Z₀ : Circuit Gate 2 := seq (List.replicate 4 T₀)
/-- `Z` on wire `1`. -/
def Z₁ : Circuit Gate 2 := seq (List.replicate 4 T₁)
abbrev CX : Circuit Gate 2 := g2 .CX
abbrev σ : Circuit Gate 2 := g2 .swap
/-- The CNOT with control on the bottom wire `0` and target on wire `1`. -/
def revCX : Circuit Gate 2 := seq [σ, CX, σ]

/-! ### Three wires -/

namespace W3

abbrev T₀ : Circuit Gate 3 := g1 .T
abbrev T₁ : Circuit Gate 3 := shift (g1 .T)
abbrev T₂ : Circuit Gate 3 := shift (shift (g1 .T))
abbrev CX₀ : Circuit Gate 3 := g2 .CX
abbrev CX₁ : Circuit Gate 3 := shift (g2 .CX)
abbrev σ₀ : Circuit Gate 3 := g2 .swap
/-- The CNOT with control on wire `2` and target on wire `0` (Figure 9 (1)). -/
def CX₂₀ : Circuit Gate 3 := seq [σ₀, CX₁, σ₀]
/-- The phase gadget (CT) on wires `1, 0`: CNOT, `T` on the target, CNOT. -/
def CT₁₀ : Circuit Gate 3 := seq [CX₀, T₀, CX₀]
/-- The phase gadget (CT) on wires `2, 1`. -/
def CT₂₁ : Circuit Gate 3 := seq [CX₁, T₁, CX₁]
/-- The phase gadget (CT) on wires `2, 0`. -/
def CT₂₀ : Circuit Gate 3 := seq [σ₀, CT₂₁, σ₀]
/-- The phase gadget (CCT) on wires `2, 1, 0`: CNOT₂₁, CNOT₁₀, `T` on wire
`0`, CNOT₁₀, CNOT₂₁. -/
def CCT : Circuit Gate 3 := seq [CX₁, CX₀, T₀, CX₀, CX₁]

end W3

/-! ### Four wires -/

namespace W4

/-- `T` on wire `i`. -/
def t : ℕ → Circuit Gate 4
  | 0 => g1 .T
  | 1 => shift (g1 .T)
  | 2 => shift (shift (g1 .T))
  | _ => shift (shift (shift (g1 .T)))
/-- The CNOT on wires `i + 1` (control), `i` (target). -/
def cx : ℕ → Circuit Gate 4
  | 0 => g2 .CX
  | 1 => shift (g2 .CX)
  | _ => shift (shift (g2 .CX))
/-- The swap of wires `i, i + 1`. -/
def sw : ℕ → Circuit Gate 4
  | 0 => g2 .swap
  | 1 => shift (g2 .swap)
  | _ => shift (shift (g2 .swap))
/-- `c` conjugated by the swaps `p` (first `p`, then `c`, then `p` backwards). -/
def conj (c : Circuit Gate 4) (p : List (Circuit Gate 4)) : Circuit Gate 4 :=
  seq (p ++ [c] ++ p.reverse)
/-- The swaps carrying wire `b` up to wire `a - 1`. -/
def up (b a : ℕ) : List (Circuit Gate 4) := (List.range (a - 1 - b)).map fun j => sw (b + j)
/-- The phase gadget (CT) on wires `a > b`: on adjacent wires CNOT, `T` on
the lower wire, CNOT; otherwise wire `b` is first carried up next to `a`. -/
def CT (a b : ℕ) : Circuit Gate 4 := conj (seq [cx (a - 1), t (a - 1), cx (a - 1)]) (up b a)
/-- The phase gadget (CCT) on wires `a > b > c`: wire `b` is carried up next
to `a`, then `c` next to `b`. -/
def CCT (a b c : ℕ) : Circuit Gate 4 :=
  conj (seq [cx (a - 1), cx (a - 2), t (a - 2), cx (a - 2), cx (a - 1)]) (up b a ++ up c (a - 1))

end W4

/-! ### The rules of Figure 7 -/

/-- The rules of CNOTdihe₂ (Figure 7). -/
inductive Ax
  /-- (ω⁸): `ω₈^{⊗8} = id₀`. -/
  | ω8
  /-- (X²): `X X = id`. -/
  | X2
  /-- (T⁸): `T⁸ = id`. -/
  | T8
  /-- (TX): `ω₈ T† X = X T`. -/
  | TX
  /-- (XC): a CNOT followed by `X` on its target is `X` on its control
  around the CNOT. -/
  | XC
  /-- (B): a CNOT followed by a reversed CNOT is a swap followed by a CNOT. -/
  | B
  /-- (ZC): a CNOT followed by `Z` on its control is `Z` on its target
  around the CNOT. -/
  | ZC
  /-- (CPh): a CNOT, `T` on its control, a CNOT, is `T` on the top wire. -/
  | CPh
  /-- (I): the CNOT from wire `2` to wire `0` is
  `CNOT₁₀ ; CNOT₂₁ ; CNOT₁₀ ; CNOT₂₁`. -/
  | I
  /-- (C²T): two (CCT) gadgets are `T⁶ ⊗ T⁶ ⊗ T⁶` and two (CT) gadgets on each
  pair of wires. -/
  | C2T
  /-- (C³T): (CCT) on the bottom three of four wires between two CNOTs from
  the top wire is `T⁵` on each wire, three (CT) gadgets on each pair of
  wires and one (CCT) gadget on each triple. -/
  | C3T
  deriving DecidableEq

/-- The number of wires each rule is drawn on. -/
def Ax.arity : Ax → ℕ
  | .ω8 => 0
  | .X2 | .T8 | .TX => 1
  | .XC | .B | .ZC | .CPh => 2
  | .I | .C2T => 3
  | .C3T => 4

open W4 in
/-- The two sides of (C³T), wires numbered from the bottom (the figure's rows
`0, 1, 2, 3` from the top are wires `3, 2, 1, 0`). -/
def c3t : Circuit Gate 4 × Circuit Gate 4 :=
  (seq [cx 2, CCT 2 1 0, cx 2],
   seq ([seq (List.replicate 5 (t 3)), seq (List.replicate 5 (t 2)),
      seq (List.replicate 5 (t 1)), seq (List.replicate 5 (t 0))] ++
    ([(3, 2), (3, 1), (3, 0), (2, 1), (2, 0), (1, 0)].map fun p =>
      seq (List.replicate 3 (CT p.1 p.2))) ++
    [CCT 3 2 1, CCT 3 2 0, CCT 3 1 0, CCT 2 1 0]))

/-- The two sides of each rule of Figure 7, read left to right. -/
def Ax.sides : (a : Ax) → Circuit Gate a.arity × Circuit Gate a.arity
  | .ω8 => (seq (List.replicate 8 ω), 1)
  | .X2 => (seq [X, X], 1)
  | .T8 => (seq (List.replicate 8 T), 1)
  | .TX => (seq [ω, Tdg, X], seq [X, T])
  | .XC => (seq [CX, X₀], seq [X₁, CX, X₁])
  | .B => (seq [CX, revCX], seq [σ, CX])
  | .ZC => (seq [CX, Z₁], seq [Z₀, CX, Z₀])
  | .CPh => (seq [CX, T₁, CX], T₁)
  | .I => (W3.CX₂₀, seq [W3.CX₀, W3.CX₁, W3.CX₀, W3.CX₁])
  | .C2T => (seq [W3.CCT, W3.CCT],
      seq [seq (List.replicate 6 W3.T₂), seq (List.replicate 6 W3.T₁),
        seq (List.replicate 6 W3.T₀), W3.CT₂₁, W3.CT₂₁, W3.CT₂₀, W3.CT₂₀, W3.CT₁₀, W3.CT₁₀])
  | .C3T => c3t

/-- The presentation CNOTdihe₂ of Figure 7. -/
def pres : PropPresentation Gate where
  swap := .swap
  Ax := Ax
  arity := Ax.arity
  lhs a := a.sides.1
  rhs a := a.sides.2

instance : DecidableEq pres.Ax := inferInstanceAs (DecidableEq Ax)

end QCert.Minimality.CNOTDihedral
