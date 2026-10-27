/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real-Clifford+CH circuits and the equations of Figure 4

Clément, *A complete equational theory for real-Clifford+CH quantum
circuits* (arXiv:2602.06644).  The gates are those of (A): `H`, `Z`, `CZ`
and the controlled Hadamard `CH`.

## Conventions

* Wire `0` is the bottom wire of a drawing; on a `k`-wire drawing the top
  wire is wire `k - 1`.  `CH` has its control on wire `1` (the upper wire)
  and its `H` on wire `0`, as drawn in (A).
* Circuits are words in operator order (`w * v` applies `v` first), but
  every circuit below is written with `drawn`, which takes the gates in the
  order a figure draws them, left to right: `drawn [a, b]` applies `a` and
  then `b`.  So each relation reads as its figure.

## PROP and PRO

The paper works in a PROP: the swap is a generator and the topological
axioms of Figure 1 hold structurally.  The framework's circuits form a PRO
(`Lift`: shifts, disjoint gates commute), with no swap.  Remark 1 of the
paper: the result adapts to the PRO setting by adding Equations (f) and (g)
of Figure 1, and (f) may be replaced by the four equations (f1)–(f4) of
Figure 2.  We also eliminate the swap generator by Tietze: Equation (8)
expresses it through `CZ` and `H`, and we take (8) as its definition
(`swap`).  The theory is therefore Figure 4 without (8), with `swap` read as
the circuit of (8), plus (f1)–(f4) and (g) (`Rule`).

Gates on non-adjacent wires and multi-controlled gates whose target is not
at the bottom are defined in the paper by conjugation with swaps, the
network being irrelevant up to the topological rules; we fix one network
for each (`cz20`, `ch20`, the conjugations in `box` and `zx`), keeping the
vertical order of the controls as the paper's convention asks.
-/
import QCert.Circuit.Basic

namespace QCert.RealCliffordCH

open Circuit

/-- The gate set (A) of real-Clifford+CH circuits. -/
inductive Gate : ℕ → Type
  /-- The Hadamard gate. -/
  | H : Gate 1
  /-- The Pauli `Z` gate, drawn as a black dot. -/
  | Z : Gate 1
  /-- The controlled-`Z` gate. -/
  | CZ : Gate 2
  /-- The controlled-Hadamard gate: control on wire `1`, `H` on wire `0`. -/
  | CH : Gate 2

/-- Real-Clifford+CH circuits on `n` wires. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- A circuit as a figure draws it: the gates of the list from left to
right, the first one applied first. -/
def drawn {n : ℕ} (l : List (Circ n)) : Circ n := l.reverse.prod

section Gates

variable {n : ℕ}

/-- `H` on wire `0`. -/
abbrev h : Circ (n + 1) := g1 Gate.H

/-- `Z` on wire `0`. -/
abbrev z : Circ (n + 1) := g1 Gate.Z

/-- `CZ` on wires `0, 1`. -/
abbrev cz : Circ (n + 2) := g2 Gate.CZ

/-- `CH` from wire `1` onto wire `0`. -/
abbrev ch : Circ (n + 2) := g2 Gate.CH

/-- Figure 3: `X := H Z H`, drawn as `⊕`. -/
def x : Circ (n + 1) := drawn [h, z, h]

/-- Figure 3: a white dot alone on a wire, `X Z X`. -/
def zw : Circ (n + 1) := drawn [x, z, x]

/-- Equation (8), taken as the definition of the swap of wires `0, 1`. -/
def swap : Circ (n + 2) := drawn [cz, shift h, h, cz, shift h, h, cz, shift h, h]

/-- Figure 3: `CZ` with a white control on wire `1`, `X` around it. -/
def czw : Circ (n + 2) := drawn [shift x, cz, shift x]

/-- Figure 3: `CH` with a white control on wire `1`. -/
def chw : Circ (n + 2) := drawn [shift x, ch, shift x]

/-- `CZ` between wires `2` and `0`, crossing wire `1`: the `CZ` of wires
`2, 1` with the swap of wires `0, 1` on each side. -/
def cz20 : Circ (n + 3) := drawn [swap, shift cz, swap]

/-- `CH` from wire `2` onto wire `0`, crossing wire `1`. -/
def ch20 : Circ (n + 3) := drawn [swap, shift ch, swap]

/-- `CZ` between wires `2` and `0` with a white control on wire `2`. -/
def cz20w : Circ (n + 3) := drawn [shift (shift x), cz20, shift (shift x)]

/-- Section 2.2: the shortcut `P ⊗ P` on wires `0, 1`. -/
def pp : Circ (n + 2) :=
  drawn [ch, shift h, z, ch, shift h, z, ch, shift h, z, swap]

/-- The transposition of wires `0` and `2`. -/
def tau02 : Circ (n + 3) := drawn [swap, shift swap, swap]

/-- `w` conjugated by `u`, drawn `u, w, u`. -/
def conj (u w : Circ n) : Circ n := drawn [u, w, u]

end Gates

/-! ## Multi-controlled gates (Definition 2.4) -/

/-- The doubly controlled `ZX` of Definition 2.4, controls on wires `2, 1`,
target wire `0`: the recursive step at one control above the last, whose
box is the `CZ` of wires `2, 0` (`zx 2` below). -/
def zx2 : Circ 3 := drawn [ch, conj swap (shift cz), ch, conj swap (shift cz)]

/-- The doubly controlled `XZ` of Definition 2.4 (`xz 2` below). -/
def xz2 : Circ 3 := drawn [conj swap (shift cz), ch, conj swap (shift cz), ch]

/-- Definition 2.4: the multi-controlled `Z` gate with `k` controls, drawn
with a dashed box: the box on wire `0`, the controls on wires `1, …, k`.
It acts as `-1` when all its controls are `1` and leaves wire `0` alone.

* `k = 0`: `Z` and a white dot, i.e. `-I`;
* `k = 1`: `Z` on the control;
* `k = 2`: `CZ` of the two controls;
* `k + 3`: the `ZX` controlled by wires `2, 1`, the box with `k + 2`
  controls on wires `0, 3, …, k + 3` and its box on wire `1` (the box
  moved up one wire and conjugated by the transposition of wires `0, 2` on
  the bottom three wires),
  the `XZ` controlled by wires `2, 1`, and the same box again. -/
def box : (k : ℕ) → Circ (k + 1)
  | 0 => drawn [z, zw]
  | 1 => shift z
  | 2 => shift cz
  | k + 3 =>
    drawn [pad (k + 1) zx2, conj (pad (k + 1) (tau02 : Circ 3)) (shift (box (k + 2))),
      pad (k + 1) xz2, conj (pad (k + 1) (tau02 : Circ 3)) (shift (box (k + 2)))]

/-- Definition 2.4: the multi-controlled `ZX` gate with `m` controls, on
wires `1, …, m`, target wire `0`.  The recursive step uses the box with
controls on wires `0, 2, …, m` and box on wire `1`: `box m` conjugated by
the swap of wires `0, 1`. -/
def zx : (m : ℕ) → Circ (m + 1)
  | 0 => drawn [x, z]
  | m + 1 => drawn [ch, conj swap (box (m + 1)), ch, conj swap (box (m + 1))]

/-- Definition 2.4: the multi-controlled `XZ` gate with `m` controls. -/
def xz : (m : ℕ) → Circ (m + 1)
  | 0 => drawn [z, x]
  | m + 1 => drawn [conj swap (box (m + 1)), ch, conj swap (box (m + 1)), ch]

theorem zx_two : zx 2 = zx2 := rfl

theorem xz_two : xz 2 = xz2 := rfl

/-- Definition 2.4: the multi-controlled `H` gate with `k` controls, drawn
with a dashed box: the box on wire `0`, `H` on wire `1`, the controls on
wires `2, …, k + 1`. -/
def mch : (k : ℕ) → Circ (k + 2)
  | 0 => shift h
  | 1 => shift ch
  | k + 2 => drawn [pp, box (k + 3), pp]

/-! ## The equations -/

/-- The equations of Figure 4, each on the wires it is drawn on, with the
swap read as the circuit of Equation (8) (which is therefore not an
equation here), together with the equations (f1)–(f4) of Figure 2 and (g) of
Figure 1 that Remark 1 adds in the PRO setting. -/
inductive Rule : CRel Gate
  /-- (1) -/
  | e1 : Rule 1 (drawn [h, h]) (drawn [])
  /-- (2) -/
  | e2 : Rule 1 (drawn [z, z]) (drawn [])
  /-- (3) -/
  | e3 : Rule 1 (drawn [h, z] ^ 8) (drawn [])
  /-- (4) -/
  | e4 : Rule 2 (drawn [cz, cz]) (drawn [])
  /-- (5) -/
  | e5 : Rule 2 (drawn [ch, ch]) (drawn [])
  /-- (6) -/
  | e6 : Rule 2 (drawn [cz, czw]) (drawn [z])
  /-- (7) -/
  | e7 : Rule 2 (drawn [ch, chw]) (drawn [h])
  /-- (9) -/
  | e9 : Rule 2 (drawn [cz, swap]) (drawn [swap, cz])
  /-- (10) -/
  | e10 : Rule 2 (drawn [ch, czw]) (drawn [czw, ch])
  /-- (11) -/
  | e11 : Rule 2 (drawn [ch, shift h, shift z, ch, shift h])
      (drawn [shift h, shift z, ch, shift h, ch])
  /-- (12) -/
  | e12 : Rule 3 (drawn [shift cz, cz]) (drawn [cz, shift cz])
  /-- (13) -/
  | e13 : Rule 3 (drawn [shift cz, ch]) (drawn [ch, shift cz])
  /-- (14) -/
  | e14 : Rule 3 (drawn [ch, cz20, ch, cz20]) (drawn [ch20, cz, ch20, cz])
  /-- (15) -/
  | e15 : Rule 3 (drawn [ch, cz20] ^ 4) (drawn [shift cz])
  /-- (16) -/
  | e16 : Rule 3 (drawn [cz20w, ch, cz20, ch]) (drawn [ch, cz20, ch, cz20w])
  /-- (17) -/
  | e17 : Rule 3 (drawn [cz20w, ch, shift ch, ch]) (drawn [ch, shift ch, ch, cz20w])
  /-- (18) -/
  | e18 : Rule 3 (drawn [shift cz, pp]) (drawn [pp, shift ch])
  /-- (19), the schema: on `n = k + 5` wires, `Z` on wire `0` commutes with
  the multi-controlled `Z` gate whose box is on wire `0`. -/
  | e19 (k : ℕ) : Rule (k + 5) (drawn [z, box (k + 4)]) (drawn [box (k + 4), z])
  /-- (f1) -/
  | f1 : Rule 2 (drawn [shift z, swap]) (drawn [swap, z])
  /-- (f2) -/
  | f2 : Rule 2 (drawn [shift h, swap]) (drawn [swap, h])
  /-- (f3) -/
  | f3 : Rule 3 (drawn [shift cz, swap, shift swap]) (drawn [swap, shift swap, cz])
  /-- (f4) -/
  | f4 : Rule 3 (drawn [shift ch, swap, shift swap]) (drawn [swap, shift swap, ch])
  /-- (g) -/
  | g : Rule 2 (drawn [swap, swap]) (drawn [])

/-- The equational theory `QC` on `n` wires: the rules on the bottom wires
of every wider circuit, with the structural rules. -/
abbrev theory (n : ℕ) : WRel (Gen Gate n) := Lift (Padded Rule) n

end QCert.RealCliffordCH
