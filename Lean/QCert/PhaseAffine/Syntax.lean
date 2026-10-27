/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Prime-dimensional phase-affine circuits: syntax

C. Blake, *Completeness for Prime-Dimensional Phase-Affine Circuits*,
arXiv:2603.06466.  For a prime `d`, four nested fragments of qudit circuits:

* level `0`, `Aff_d` (Definition 5): the translation `X : x ↦ x + 1`, the
  multipliers `M_a : x ↦ a x` (`a ∈ 𝔽_d^×`) and the controlled addition
  `CX : (x, y) ↦ (x, x + y)`, with the rules (1)–(8) of Figure 1;
* level `1`, `LinPhase_d` (Definition 14): adds the scalar `ω` and the phase
  `Z` (exponent `x`), with the rules (19)–(23) of Figure 3;
* level `2`, `QuadPhase_d` (`d` odd): adds `S` (exponent `binom x 2`), with
  the rules (24)–(30) of Figure 4;
* level `3`, `CubicPhase_d` (`d > 3`): adds `T` (exponent `binom x 3`), with
  the rules (31)–(42) of Figure 5.

Each level keeps the gates and rules of the levels below.

## Conventions

* Wires are numbered from `0` at the bottom of a diagram.  The paper's
  two-wire `CX` has its control on the top wire and its target on the bottom
  wire, so here `CX` is the two-wire gate with control wire `1` and target
  wire `0`.  On three wires the paper's top, middle and bottom wires are the
  wires `2`, `1`, `0`; on four wires (rule (41)) the wires `3`, `2`, `1`, `0`.
* A circuit is a word in operator order (`w * v` applies `v` first).  The
  paper draws diagrams from left to right; `seq [g₁, …, gₖ]` is the diagram
  that applies `g₁` first, i.e. the word `gₖ * ⋯ * g₁`, so that every rule
  below reads left to right as it is drawn.  Gates drawn in the same column
  on disjoint wires are listed from top to bottom.
* An iterate whose label is an element `k ∈ 𝔽_d` (the paper's labelled
  gates, e.g. `X^x`, `CX^{-x}`, `S^{x²}`, `Z^{binom x 2}`) is the
  `k.val`-fold iterate, `w ^ᶠ k`; for `1 ≤ k ≤ d - 1` the label `-k` is then
  the `(d - k)`-fold iterate, the paper's convention for negative labels
  (Definition 5 and Definition 15).  Unlabelled iterates `w ^ m` (`Z^d`) are
  iterates by a natural number.
* The paper's circuits form a PROP with structural swaps.  The framework has
  no built-in symmetry, so the crossing `SWAP` is a two-wire gate, and the
  laws of the symmetry are rules of every level: `SWAP` is an involution and
  it is natural for every generator (`swap_nat1`, `swap_nat2`; at the gate
  `SWAP` the latter is the Yang–Baxter equation).  Together with the
  framework's structural rules (an equation may be moved up a wire, gates on
  disjoint wires commute, a scalar is the same on every wire) these present
  the free PROP on the generators.  A gate drawn on wires that are not
  adjacent, or upside down, is a *placed instance* (Section 3.7): the gate on
  adjacent wires conjugated by swaps (`flip`, `long`, `long3` below).
-/
import QCert.Circuit.Basic
import Mathlib.Data.ZMod.Basic

namespace QCert.PhaseAffine

/-- The gates.  `lv` is the level of the fragment (`0` affine, `1` linear,
`2` quadratic, `3` cubic phases); a phase gate carries the evidence that the
fragment contains it. -/
inductive Gate (d lv : ℕ) : ℕ → Type
  /-- The global phase `ω` (Definition 14). -/
  | omega (h : 1 ≤ lv) : Gate d lv 0
  /-- The translation `X : x ↦ x + 1` (Definition 5). -/
  | X : Gate d lv 1
  /-- The multiplier `M_a : x ↦ a x`, `a ∈ 𝔽_d^×` (Definition 5). -/
  | M (a : (ZMod d)ˣ) : Gate d lv 1
  /-- The phase `Z`, exponent `x` (Definition 14). -/
  | Z (h : 1 ≤ lv) : Gate d lv 1
  /-- The phase `S`, exponent `binom x 2` (Definition 14). -/
  | S (h : 2 ≤ lv) : Gate d lv 1
  /-- The phase `T`, exponent `binom x 3` (Definition 14). -/
  | T (h : 3 ≤ lv) : Gate d lv 1
  /-- The controlled addition `CX : (x, y) ↦ (x, x + y)`, control on wire `1`
  (the paper's top wire), target on wire `0` (Definition 5). -/
  | CX : Gate d lv 2
  /-- The crossing, the symmetry `σ_{1,1}` of the PROP. -/
  | SWAP : Gate d lv 2

/-- Circuits on `n` wires of the fragment of level `lv`. -/
abbrev C (d lv n : ℕ) := Circuit (Gate d lv) n

section Words

variable {d lv : ℕ}

/-- A diagram read from left to right: `seq [g₁, …, gₖ]` applies `g₁` first,
the word `gₖ * ⋯ * g₁`. -/
def seq {n : ℕ} (l : List (C d lv n)) : C d lv n := l.reverse.prod

@[simp] theorem seq_nil {n : ℕ} : seq ([] : List (C d lv n)) = 1 := rfl

@[simp] theorem seq_cons {n : ℕ} (g : C d lv n) (l : List (C d lv n)) :
    seq (g :: l) = seq l * g := by
  simp [seq]

/-- The iterate of a circuit labelled by `k ∈ 𝔽_d`: the `k.val`-fold
iterate. -/
def fpow {n : ℕ} (w : C d lv n) (k : ZMod d) : C d lv n := w ^ k.val

@[inherit_doc] infixr:75 " ^ᶠ " => fpow

/-! ### The generators as circuits on their own wires -/

/-- `ω`, at any width. -/
abbrev ω {n : ℕ} (h : 1 ≤ lv) : C d lv n := Circuit.g0 (Gate.omega h)
/-- `X` on one wire. -/
abbrev X : C d lv 1 := Circuit.g1 Gate.X
/-- `M_a` on one wire. -/
abbrev M (a : (ZMod d)ˣ) : C d lv 1 := Circuit.g1 (Gate.M a)
/-- `Z` on one wire. -/
abbrev Z (h : 1 ≤ lv) : C d lv 1 := Circuit.g1 (Gate.Z h)
/-- `S` on one wire. -/
abbrev S (h : 2 ≤ lv) : C d lv 1 := Circuit.g1 (Gate.S h)
/-- `T` on one wire. -/
abbrev T (h : 3 ≤ lv) : C d lv 1 := Circuit.g1 (Gate.T h)
/-- `CX` on two wires: control wire `1`, target wire `0`. -/
abbrev CX : C d lv 2 := Circuit.g2 Gate.CX
/-- The crossing on two wires. -/
abbrev SW : C d lv 2 := Circuit.g2 Gate.SWAP

/-! ### Placements -/

/-- A one-wire circuit on the top wire of two. -/
abbrev top (w : C d lv 1) : C d lv 2 := Circuit.shift w
/-- A one-wire circuit on the bottom wire of two. -/
abbrev bot (w : C d lv 1) : C d lv 2 := Circuit.pad 1 w

/-- A two-wire circuit upside down: its top wire on wire `0`, its bottom
wire on wire `1` (conjugated by the crossing). -/
def flip (w : C d lv 2) : C d lv 2 := seq [SW, w, SW]

/-- A two-wire circuit placed on the wires `2` (its top wire) and `0` (its
bottom wire) of three, conjugated by the crossing of the wires `1, 2`. -/
def long (w : C d lv 2) : C d lv 3 := seq [Circuit.shift SW, Circuit.pad 1 w, Circuit.shift SW]

/-- A three-wire circuit placed on the wires `3, 1, 0` of four (its top wire
on wire `3`), conjugated by the crossing of the wires `2, 3`. -/
def long3 (w : C d lv 3) : C d lv 4 :=
  seq [Circuit.shift (Circuit.shift SW), Circuit.pad 1 w, Circuit.shift (Circuit.shift SW)]

/-- The cyclic permutation of three wires carrying the contents of the wires
`0, 1, 2` to the wires `1, 2, 0` (`σ_{2,1}`): the crossing of the wires
`1, 2`, then that of the wires `0, 1`. -/
def cyc : C d lv 3 := seq [Circuit.shift SW, Circuit.pad 1 SW]

/-! ### Binomial coordinates in `𝔽_d` -/

/-- `binom x 2 = x (x - 1) / 2` in `𝔽_d` (Section 3.2). -/
def binom2 (x : ZMod d) : ZMod d := x * (x - 1) * (2 : ZMod d)⁻¹

/-- `binom x 3 = x (x - 1) (x - 2) / 6` in `𝔽_d` (Section 3.2). -/
def binom3 (x : ZMod d) : ZMod d := x * (x - 1) * (x - 2) * (6 : ZMod d)⁻¹

/-! ### The derived diagonals (Definitions 16, 17, 18) -/

/-- Definition 16, the bilinear diagonal `CZ` (exponent `x y`): `CX`, `S` on
the bottom wire, `CX^{-1}`, then `S^{-1}` on both wires. -/
def CZ (h : 2 ≤ lv) : C d lv 2 :=
  seq [CX, bot (S h), CX ^ᶠ (-1), top (S h ^ᶠ (-1)), bot (S h ^ᶠ (-1))]

/-- Definition 17, the controlled square `CS` (exponent `x binom y 2`, `x`
on the control, the top wire, `y` on the bottom wire), with `t = 2⁻¹`. -/
def CS (h : 3 ≤ lv) : C d lv 2 :=
  let t : ZMod d := (2 : ZMod d)⁻¹
  seq [CZ (by omega) ^ᶠ t, top (Z (by omega) ^ᶠ (-t)), top (T h ^ᶠ (-1)),
    top (S (by omega) ^ᶠ (-1)), CX, bot (T h ^ᶠ t), CX ^ᶠ (-1), CX ^ᶠ (-1),
    bot (T h ^ᶠ (-t)), CX]

/-- Definition 17, the flip `SC` of `CS` (exponent `y binom x 2`). -/
def SC (h : 3 ≤ lv) : C d lv 2 := flip (CS h)

/-- Definition 18, the trilinear diagonal `CCZ` (exponent `x y z`) on three
wires. -/
def CCZ (h : 3 ≤ lv) : C d lv 3 :=
  -- `T` and `T^{-1}` on the bottom, middle and top wires
  let T0 : C d lv 3 := Circuit.pad 2 (T h)
  let T0' : C d lv 3 := Circuit.pad 2 (T h ^ᶠ (-1))
  let T1 : C d lv 3 := Circuit.pad 1 (Circuit.shift (T h))
  let T1' : C d lv 3 := Circuit.pad 1 (Circuit.shift (T h ^ᶠ (-1)))
  let T2 : C d lv 3 := Circuit.shift (Circuit.shift (T h))
  -- `CX` and `CX^{-1}` from the top wire to the middle wire
  let A : C d lv 3 := Circuit.shift CX
  let A' : C d lv 3 := Circuit.shift (CX ^ᶠ (-1))
  -- `CX` and `CX^{-1}` from the middle wire to the bottom wire
  let B : C d lv 3 := Circuit.pad 1 CX
  let B' : C d lv 3 := Circuit.pad 1 (CX ^ᶠ (-1))
  seq [A, B, T0, B', A', A, T1', A', B, T0', B', long CX, T0', long (CX ^ᶠ (-1)), T2, T1, T0]

end Words

/-! ### The rules -/

open Circuit in
/-- The rules of the fragment of level `lv`, each on the wires it is drawn
on, read left to right (`seq`).  The names `rN` are the paper's equation
numbers. -/
inductive Rules (d lv : ℕ) : CRel (Gate d lv)
  -- Figure 1, the rule set `Aff_d`.
  /-- (1) `M_1 = id`. -/
  | r1 : Rules d lv 1 (M 1) 1
  /-- (2) `M_x` then `M_y` is `M_{xy}`. -/
  | r2 (x y : (ZMod d)ˣ) : Rules d lv 1 (seq [M x, M y]) (M (x * y))
  /-- (3) `X^{-1}`, `M_x`, `X^x` is `M_x`. -/
  | r3 (x : (ZMod d)ˣ) : Rules d lv 1 (seq [X ^ᶠ (-1), M x, X ^ᶠ (x : ZMod d)]) (M x)
  /-- (4) `M_x` on the control, then `CX`, is `CX^x`, then `M_x` on the control. -/
  | r4 (x : (ZMod d)ˣ) : Rules d lv 2 (seq [top (M x), CX]) (seq [CX ^ᶠ (x : ZMod d), top (M x)])
  /-- (5) `CX`, `M_x` on the target, `CX^{-x}` is `M_x` on the target. -/
  | r5 (x : (ZMod d)ˣ) :
      Rules d lv 2 (seq [CX, bot (M x), CX ^ᶠ (-(x : ZMod d))]) (bot (M x))
  /-- (6) `X` on the control, then `CX`, is `CX`, then `X` on both wires. -/
  | r6 : Rules d lv 2 (seq [top X, CX]) (seq [CX, top X, bot X])
  /-- (7) the crossing is `CX^{-1}` upside down, `CX`, `CX^{-1}` upside down,
  then `M_{-1}` on the top wire. -/
  | r7 : Rules d lv 2 SW (seq [flip (CX ^ᶠ (-1)), CX, flip (CX ^ᶠ (-1)), top (M (-1))])
  /-- (8) on three wires: `CX` from the top wire to the bottom wire, `CX` from
  the middle wire to the bottom wire, `CX` from the top wire to the middle
  wire is `CX` from the top wire to the middle wire, then `CX` from the
  middle wire to the bottom wire. -/
  | r8 : Rules d lv 3 (seq [long CX, pad 1 CX, shift CX]) (seq [shift CX, pad 1 CX])
  -- The symmetry of the PROP.
  /-- The crossing is an involution. -/
  | swap_inv : Rules d lv 2 (seq [SW, SW]) 1
  /-- The crossing is natural for one-wire generators. -/
  | swap_nat1 (g : Gate d lv 1) : Rules d lv 2 (seq [bot (g1 g), SW]) (seq [SW, top (g1 g)])
  /-- The crossing is natural for two-wire generators (`σ_{2,1}` is `cyc`);
  at `g = SWAP` this is the Yang–Baxter equation. -/
  | swap_nat2 (g : Gate d lv 2) :
      Rules d lv 3 (seq [pad 1 (g2 (n := 0) g), cyc]) (seq [cyc, shift (g2 (n := 0) g)])
  -- Figure 3, `LinPhase_d`.
  /-- (19) `ω^d` is the empty diagram. -/
  | r19 (h : 1 ≤ lv) : Rules d lv 0 (ω h ^ d) 1
  /-- (20) `Z^d = id`. -/
  | r20 (h : 1 ≤ lv) : Rules d lv 1 (Z h ^ d) 1
  /-- (21) `Z` on both wires, then `CX`, is `CX`, then `Z` on the target. -/
  | r21 (h : 1 ≤ lv) : Rules d lv 2 (seq [top (Z h), bot (Z h), CX]) (seq [CX, bot (Z h)])
  /-- (22) `M_x`, `Z` is `Z^x`, `M_x`. -/
  | r22 (h : 1 ≤ lv) (x : (ZMod d)ˣ) :
      Rules d lv 1 (seq [M x, Z h]) (seq [Z h ^ᶠ (x : ZMod d), M x])
  /-- (23) `X`, `Z` is `Z`, `X`, `ω`. -/
  | r23 (h : 1 ≤ lv) : Rules d lv 1 (seq [X, Z h]) (seq [Z h, X, ω h])
  -- Figure 4, `QuadPhase_d`.
  /-- (24) `S^d = id`. -/
  | r24 (h : 2 ≤ lv) : Rules d lv 1 (S h ^ d) 1
  /-- (25) `X`, `S` is `S`, `Z`, `X`. -/
  | r25 (h : 2 ≤ lv) : Rules d lv 1 (seq [X, S h]) (seq [S h, Z (by omega), X])
  /-- (26) `Z`, `S` is `S`, `Z`. -/
  | r26 (h : 2 ≤ lv) : Rules d lv 1 (seq [Z (by omega), S h]) (seq [S h, Z (by omega)])
  /-- (27) `M_x`, `S` is `S^{x²}`, `Z^{binom x 2}`, `M_x`. -/
  | r27 (h : 2 ≤ lv) (x : (ZMod d)ˣ) :
      Rules d lv 1 (seq [M x, S h])
        (seq [S h ^ᶠ ((x : ZMod d) ^ 2), Z (by omega) ^ᶠ binom2 (x : ZMod d), M x])
  /-- (28) `M_{-1}` on the top wire, `CZ^{-1}`, `M_{-1}` on the top wire is `CZ`. -/
  | r28 (h : 2 ≤ lv) : Rules d lv 2 (seq [top (M (-1)), CZ h ^ᶠ (-1), top (M (-1))]) (CZ h)
  /-- (29) `S` on the control, then `CX`, is `CX`, then `S` on the control. -/
  | r29 (h : 2 ≤ lv) : Rules d lv 2 (seq [top (S h), CX]) (seq [CX, top (S h)])
  /-- (30) on three wires: `CX` from the top wire to the middle wire, then `CZ`
  on the middle and bottom wires, is `CZ` on the top and bottom wires, `CZ` on
  the middle and bottom wires, then the `CX`. -/
  | r30 (h : 2 ≤ lv) :
      Rules d lv 3 (seq [shift CX, pad 1 (CZ h)]) (seq [long (CZ h), pad 1 (CZ h), shift CX])
  -- Figure 5, `CubicPhase_d`.
  /-- (31) `T^d = id`. -/
  | r31 (h : 3 ≤ lv) : Rules d lv 1 (T h ^ d) 1
  /-- (32) `T^{x³}`, `Z^{binom x 3}`, `S^{2x binom x 2}`, `M_x` is `M_x`, `T`. -/
  | r32 (h : 3 ≤ lv) (x : (ZMod d)ˣ) :
      Rules d lv 1
        (seq [T h ^ᶠ ((x : ZMod d) ^ 3), Z (by omega) ^ᶠ binom3 (x : ZMod d),
          S (by omega) ^ᶠ (2 * (x : ZMod d) * binom2 (x : ZMod d)), M x])
        (seq [M x, T h])
  /-- (33) `S`, `T` is `T`, `S`. -/
  | r33 (h : 3 ≤ lv) : Rules d lv 1 (seq [S (by omega), T h]) (seq [T h, S (by omega)])
  /-- (34) `X`, `T` is `S`, `T`, `X`. -/
  | r34 (h : 3 ≤ lv) : Rules d lv 1 (seq [X, T h]) (seq [S (by omega), T h, X])
  /-- (35) `CS^{a²}`, `CZ^μ` with `μ = binom a 2`, `M_a` on the bottom wire is
  `M_a` on the bottom wire, then `CS`. -/
  | r35 (h : 3 ≤ lv) (a : (ZMod d)ˣ) :
      Rules d lv 2
        (seq [CS h ^ᶠ ((a : ZMod d) ^ 2), CZ (by omega) ^ᶠ binom2 (a : ZMod d), bot (M a)])
        (seq [bot (M a), CS h])
  /-- (36) `Z`, `T` is `T`, `Z`. -/
  | r36 (h : 3 ≤ lv) : Rules d lv 1 (seq [Z (by omega), T h]) (seq [T h, Z (by omega)])
  /-- (37) `CS^x`, then `M_x` on the control, is `M_x` on the control, then `CS`. -/
  | r37 (h : 3 ≤ lv) (x : (ZMod d)ˣ) :
      Rules d lv 2 (seq [CS h ^ᶠ (x : ZMod d), top (M x)]) (seq [top (M x), CS h])
  /-- (38) on three wires: `CCZ`, `CS` from the top wire to the middle wire,
  `CS` from the top wire to the bottom wire, `CX` from the middle wire to the
  bottom wire is that `CX`, then `CS` from the top wire to the bottom wire. -/
  | r38 (h : 3 ≤ lv) :
      Rules d lv 3 (seq [CCZ h, shift (CS h), long (CS h), pad 1 CX])
        (seq [pad 1 CX, long (CS h)])
  /-- (39) `T` on the control, then `CX`, is `CX`, then `T` on the control. -/
  | r39 (h : 3 ≤ lv) : Rules d lv 2 (seq [top (T h), CX]) (seq [CX, top (T h)])
  /-- (40) `CCZ^x`, then `M_x` on the top wire, is `M_x` on the top wire, then
  `CCZ`. -/
  | r40 (h : 3 ≤ lv) (x : (ZMod d)ˣ) :
      Rules d lv 3 (seq [CCZ h ^ᶠ (x : ZMod d), shift (shift (M x))])
        (seq [shift (shift (M x)), CCZ h])
  /-- (41) on four wires: `CCZ` on the wires `2, 1, 0`, `CCZ` on the wires
  `3, 1, 0`, `CX` from wire `3` to wire `2` is that `CX`, then `CCZ` on the
  wires `2, 1, 0`. -/
  | r41 (h : 3 ≤ lv) :
      Rules d lv 4 (seq [pad 1 (CCZ h), long3 (CCZ h), shift (shift CX)])
        (seq [shift (shift CX), pad 1 (CCZ h)])
  /-- (42) on three wires: `CS` from the top wire to the bottom wire, `CS` from
  the middle wire to the bottom wire, `CX` from the top wire to the middle
  wire is that `CX`, then `CS` from the middle wire to the bottom wire. -/
  | r42 (h : 3 ≤ lv) :
      Rules d lv 3 (seq [long (CS h), pad 1 (CS h), shift CX]) (seq [shift CX, pad 1 (CS h)])

/-- The equational theory of the fragment of level `lv` on `n` wires: the
rules on the bottom wires of every wider circuit, closed under the
structural rules. -/
abbrev theory (d lv : ℕ) : CRel (Gate d lv) := Lift (Padded (Rules d lv))

end QCert.PhaseAffine
