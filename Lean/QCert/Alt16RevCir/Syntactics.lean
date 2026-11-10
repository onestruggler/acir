/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The alternating group 𝔄₁₆ as reversible circuits on four wires: the gates, the cycles and the translated relation

Translation of `Syntactics.agda`: the gates `X`, `CX`, `CCX` and `Ex`, the
cycles `Ω 0, …, Ω 13`, and the relations that Lafont's presentation of 𝔄₁₆
translates into.

The circuits on four wires over NOT, CNOT and Toffoli, with the swap of two
adjacent wires as a fourth gate, carry out exactly the even permutations of
the sixteen states of the wires.  Lafont's Theorem 4 (`Lib/Alternating`)
presents the even permutations of sixteen points by the fourteen cycles
`ω₀, …, ω₁₃`, where `ωᵢ` sends `i` to `i + 1`, `i + 1` to `i + 2` and
`i + 2` to `i`.  This module is the circuits' side of a Reidemeister–Schreier
step from that presentation.  The generators are translated in both
directions (`Translation`): each `ωᵢ` is read as a circuit `Ω i`, and each
gate as a word in the `ωᵢ`.  The relations are translated: the rules below
are Lafont's, read between the `Ω i`, and one for each gate, which says
which word in the `Ω i` the gate is.  And the two sets of relations are
proved equivalent (`Iso`).

States.  A state is a vector of four bits, the bit of wire 0 first.  The
sixteen states are numbered along the reflected Gray code, wire 0 changing
most often; written with wire 3 first,

     0 0000    4 0110     8 1100    12 1010
     1 0001    5 0111     9 1101    13 1011
     2 0011    6 0101    10 1111    14 1001
     3 0010    7 0100    11 1110    15 1000

Two consecutive states differ on one wire, so the states `i`, `i + 1` and
`i + 2` are three corners of a face of the 4-cube, the other two wires
fixed, and the cycle of them is a doubly controlled cycle of three states
of two wires: the commutator of two Toffoli gates.

Wires and order.  Wire 0 is the bottom wire.  `CX` has its control on wire
1 and its target on wire 0, `CCX` its controls on wires 1 and 2 and its
target on wire 0, and `Ex` swaps the wires 0 and 1; `shift w` (the Agda's
`w ↑`) is `w` one wire up.  Words are in diagram order: `w * v` is `w`
followed by `v`.

The swap is structural: `Ex` is the designated swap of `CircuitProp`
(`HasSwap Gate`).  The relation `VRel SRel n` consists of the rules below
(`srel_rule`), the laws of the symmetry (`sym_rule`: the swap is an
involution, and natural in every gate) and the structural rules of
`QCert.Lift`.

Names.  The Agda's `Gen n` and `Circuit n` are `Gn n` and `Circ n` (the
framework's `QCert.Gen` and `QCert.Circuit` being visible from this
namespace), `X-gate` is `Gate.X_gate`, the relation `_SRel,_===_` is `SRel`,
and `n ⊢ w ≈ v` is notation for `CircuitProp.Der SRel n w v`.  The Agda's
`1 + i`, `2 + i` are `i + 1`, `i + 2`.
-/
import QCert.Alt16RevCir.Lib.CircuitProp

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp

/-! ## Gates -/

/-- The gates: NOT, CNOT, the swap of two adjacent wires, and Toffoli. -/
inductive Gate : ℕ → Type
  | X_gate : Gate 1
  | CX_gate : Gate 2
  | Ex_gate : Gate 2
  | CCX_gate : Gate 3

/-- `Ex` is the designated swap (the Agda's `open import Circuit.Prop Gate Ex-gate`). -/
instance : HasSwap Gate := ⟨Gate.Ex_gate⟩

/-- Generators of `n`-wire circuits (the Agda's `Gen n`). -/
abbrev Gn (n : ℕ) : Type := QCert.Gen Gate n

/-- Circuits on `n` wires (the Agda's `Circuit n`). -/
abbrev Circ (n : ℕ) : Type := QCert.Circuit Gate n

variable {n : ℕ}

/-! The generators as one-letter circuits.  `Ex` is `CircuitProp`'s `σ`. -/

abbrev X : Circ (n + 1) := g1 Gate.X_gate

abbrev CX : Circ (n + 2) := g2 Gate.CX_gate

abbrev Ex : Circ (n + 2) := g2 Gate.Ex_gate

abbrev CCX : Circ (n + 3) := g3 Gate.CCX_gate

/-! ## NOT and the swap on each wire of four -/

abbrev X₀ : Circ 4 := X

abbrev X₁ : Circ 4 := shift X

abbrev X₂ : Circ 4 := shift (shift X)

abbrev X₃ : Circ 4 := shift (shift (shift X))

abbrev Ex₀ : Circ 4 := Ex

abbrev Ex₁ : Circ 4 := shift Ex

abbrev Ex₂ : Circ 4 := shift (shift Ex)

/-! ## The cycle on a face

Between the swaps of the wires 0 1 and 2 3 the Toffoli gate has its target
on wire 1 and its controls on wires 0 and 3, so the square of
`Ex₀ * Ex₂ * CCX` is that gate followed by `CCX`, and its fourth power is
the commutator of the two.  With the wires 2 and 3 set it cycles the states
01, 11, 10 of the wires 1 0, and it does nothing otherwise: `K` is the cycle
of the states 9, 10 and 11. -/

def K : Circ 4 := (Ex₀ * Ex₂ * CCX) ^ 4

/-! `K` on the other faces.  `Kₐᵦ` cycles `x`, `x + eₐ` and `x + eₐ + eᵦ`,
where `x` is the state with wire `a` clear and the other three wires set:
`K₁₀` is `K`, and swaps carry it to the other pairs of wires. -/

def K₁₀ : Circ 4 := K

def K₀₁ : Circ 4 := Ex₀ * K₁₀ * Ex₀

def K₂₀ : Circ 4 := Ex₁ * K₁₀ * Ex₁

def K₀₂ : Circ 4 := Ex₁ * K₀₁ * Ex₁

def K₃₀ : Circ 4 := Ex₂ * K₂₀ * Ex₂

def K₀₃ : Circ 4 := Ex₂ * K₀₂ * Ex₂

/-! ## The cycles of three consecutive states -/

/-- `Ω i` cycles the states `i`, `i + 1` and `i + 2`.  If wire `a` changes
from state `i` to state `i + 1`, and wire `b` from `i + 1` to `i + 2`, it is
`Kₐᵦ` between NOT gates on the wires where state `i` differs from the first
state of `Kₐᵦ`.  Beyond 13 there is no cycle, and `Ω` is the empty circuit. -/
def Ω : ℕ → Circ 4
  | 0 => X₁ * X₂ * X₃ * K₀₁ * X₃ * X₂ * X₁
  | 1 => X₂ * X₃ * K₁₀ * X₃ * X₂
  | 2 => X₀ * X₂ * X₃ * K₀₂ * X₃ * X₂ * X₀
  | 3 => X₀ * X₃ * K₂₀ * X₃ * X₀
  | 4 => X₃ * K₀₁ * X₃
  | 5 => X₁ * X₃ * K₁₀ * X₃ * X₁
  | 6 => X₀ * X₁ * X₃ * K₀₃ * X₃ * X₁ * X₀
  | 7 => X₀ * X₁ * K₃₀ * X₁ * X₀
  | 8 => X₁ * K₀₁ * X₁
  | 9 => K₁₀
  | 10 => X₀ * K₀₂ * X₀
  | 11 => X₀ * X₂ * K₂₀ * X₂ * X₀
  | 12 => X₂ * K₀₁ * X₂
  | 13 => X₁ * X₂ * K₁₀ * X₂ * X₁
  | _ => 1

/-! ## The relations

`order`, `near` and `far` are the relations of Lafont's Theorem 4, and
`apart` his commutation of two cycles three or more points apart (the
structural rule `comm3` of his circuits), each at every position among
sixteen points.  The other six say which permutation of the states each
gate is, as a word in the cycles: the double transposition
`(i i+1)(i+2 i+3)` is `Ω (i + 1) * Ω i`, NOT on wire 0 exchanges the states
`2 i` and `2 i + 1`, and so on.  The word for `Ex₂` has one letter for every
two inversions of its permutation, the fewest possible. -/

/-- The translated relation, on four wires. -/
inductive SRel : CRel Gate
  -- Lafont's relations between the cycles.
  | order (i : ℕ) : i ≤ 13 → SRel 4 (Ω i * Ω i * Ω i) 1
  | near (i : ℕ) : i ≤ 12 → SRel 4 (Ω i * Ω (i + 1) * Ω i) (Ω (i + 1) * Ω (i + 1))
  | far (i : ℕ) : i ≤ 11 → SRel 4 (Ω i * Ω (i + 2) * Ω i) (Ω (i + 2) * Ω i * Ω (i + 1))
  | apart (i j : ℕ) : i + 3 ≤ j → j ≤ 13 → SRel 4 (Ω j * Ω i) (Ω i * Ω j)
  -- The gates as words in the cycles.
  | gate_X : SRel 4 X₀ (Ω 1 * Ω 0 * Ω 5 * Ω 4 * Ω 9 * Ω 8 * Ω 13 * Ω 12)
  | gate_CX : SRel 4 CX (Ω 3 * Ω 2 * Ω 11 * Ω 10)
  | gate_CCX : SRel 4 CCX (Ω 5 * Ω 4 * Ω 7 * Ω 6 * Ω 9 * Ω 8)
  | gate_Ex₀ : SRel 4 Ex₀ (Ω 1 * Ω 3 * Ω 2 * Ω 4 * Ω 9 * Ω 11 * Ω 10 * Ω 12)
  | gate_Ex₁ : SRel 4 Ex₁
      (Ω 2 * Ω 3 * Ω 4 * Ω 2 * Ω 5 * Ω 3 * Ω 8 * Ω 9 * Ω 10 * Ω 8 * Ω 11 * Ω 9)
  | gate_Ex₂ : SRel 4 Ex₂
      (Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 10 * Ω 11 * Ω 12 * Ω 13 *
       Ω 4 * Ω 5 * Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 10 * Ω 11 *
       Ω 6 * Ω 7 * Ω 8 * Ω 9 * Ω 4 * Ω 5 * Ω 6 * Ω 7)

/-- The congruence the translated relation generates with the swap rules
and the structural rules, at width `n` (the Agda's `n ⊢ w ≈ v`). -/
scoped notation:50 n:51 " ⊢ " w:51 " ≈ " v:51 => CircuitProp.Der SRel n w v

end QCert.Alt16RevCir
