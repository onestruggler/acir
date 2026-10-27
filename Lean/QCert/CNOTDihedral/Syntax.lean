/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: gates and relations

M. Amy, J. Chen and N. J. Ross, *A finite presentation of CNOT-dihedral
operators*, QPL 2017 (EPTCS 266, 2018), arXiv:1701.00140.

The generators (Definition 3.1) are the scalar `ω = e^{iπ/4}` and the gates
`X`, `T` and `CNOT`; the presentation is one of a symmetric monoidal
groupoid (§2), so the symmetry `SWAP` is a generator as well and its laws
(§2: involutive, natural, coherent) are rules.  The relations are
`R₁`–`R₁₃` of Figure 1.

**Wires.**  A diagram is drawn with wires at heights `y = 0, 1.6, 3.2, 4.8`;
the wire at height `0` is our wire `0` (the bottom wire), the one at `1.6`
wire `1`, and so on.  The `CNOT` of the paper is drawn with its control on
the upper wire: `CX₁₀` is the generator `CX`, control on wire `1` and target
on wire `0` (its matrix in Definition 3.1 is read with the upper wire as the
most significant bit).  Gates on non-adjacent wires are, as in the paper
(§3, the figure before Definition 3.4), the gate on the top-most wires
conjugated by `SWAP` gates: the lower wires of the gate are brought up
against its top wire by adjacent swaps.

**Order.**  Circuits are words in operator order (`w * v` applies `v`
first); `tseq [c₁, c₂, …]` writes a circuit in the time order of a diagram,
`c₁` first.
-/
import QCert.Circuit.Basic

namespace QCert.CNOTDihedral

open Circuit

/-- The gates (Definition 3.1, with the symmetry `SW` of §2). -/
inductive Gate : ℕ → Type
  /-- The scalar `ω = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- The `X` gate. -/
  | X : Gate 1
  /-- The `T` gate, `diag(1, ω)`. -/
  | T : Gate 1
  /-- `CNOT`, control on wire `1`, target on wire `0`. -/
  | CX : Gate 2
  /-- The symmetry `SWAP`. -/
  | SW : Gate 2
  deriving DecidableEq

/-- Circuits over the CNOT-dihedral gates. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- A circuit written in time order: the first circuit of the list is
applied first. -/
def tseq {n : ℕ} : List (Circ n) → Circ n
  | [] => 1
  | c :: cs => tseq cs * c

/-! ### Gates on given wires -/

/-- The scalar `ω`. -/
abbrev om {n : ℕ} : Circ n := g0 Gate.ω
/-- `X` on wire `0`. -/
abbrev X₀ {n : ℕ} : Circ (n + 1) := g1 Gate.X
/-- `X` on wire `1`. -/
abbrev X₁ {n : ℕ} : Circ (n + 2) := shift X₀
/-- `T` on wire `0`. -/
abbrev T₀ {n : ℕ} : Circ (n + 1) := g1 Gate.T
/-- `T` on wire `1`. -/
abbrev T₁ {n : ℕ} : Circ (n + 2) := shift T₀
/-- `T` on wire `2`. -/
abbrev T₂ {n : ℕ} : Circ (n + 3) := shift T₁
/-- `T` on wire `3`. -/
abbrev T₃ {n : ℕ} : Circ (n + 4) := shift T₂
/-- `CNOT`, control on wire `1`, target on wire `0`. -/
abbrev CX₁₀ {n : ℕ} : Circ (n + 2) := g2 Gate.CX
/-- `CNOT`, control on wire `2`, target on wire `1`. -/
abbrev CX₂₁ {n : ℕ} : Circ (n + 3) := shift CX₁₀
/-- `CNOT`, control on wire `3`, target on wire `2`. -/
abbrev CX₃₂ {n : ℕ} : Circ (n + 4) := shift CX₂₁
/-- `SWAP` on wires `0, 1`. -/
abbrev SW₀₁ {n : ℕ} : Circ (n + 2) := g2 Gate.SW
/-- `SWAP` on wires `1, 2`. -/
abbrev SW₁₂ {n : ℕ} : Circ (n + 3) := shift SW₀₁
/-- `SWAP` on wires `2, 3`. -/
abbrev SW₂₃ {n : ℕ} : Circ (n + 4) := shift SW₁₂

/-- `CNOT`, control on wire `2`, target on wire `0`: `CX₂₁` conjugated by the
swap of wires `0, 1` (§3, gates on non-adjacent qubits). -/
def CX₂₀ {n : ℕ} : Circ (n + 3) := tseq [SW₀₁, CX₂₁, SW₀₁]

/-! ### The derived generators (Definition 3.2) -/

/-- `U` on wires `0, 1` (Definition 3.2): `CNOT`, `T` on the target, `CNOT`;
it acts by `ω^{x₀ ⊕ x₁}`. -/
def U₀₁ {n : ℕ} : Circ (n + 2) := tseq [CX₁₀, T₀, CX₁₀]
/-- `U` on wires `1, 2`. -/
def U₁₂ {n : ℕ} : Circ (n + 3) := shift U₀₁
/-- `U` on wires `2, 3`. -/
def U₂₃ {n : ℕ} : Circ (n + 4) := shift U₁₂
/-- `U` on wires `0, 2`. -/
def U₀₂ {n : ℕ} : Circ (n + 3) := tseq [SW₀₁, U₁₂, SW₀₁]
/-- `U` on wires `1, 3`. -/
def U₁₃ {n : ℕ} : Circ (n + 4) := tseq [SW₁₂, U₂₃, SW₁₂]
/-- `U` on wires `0, 3`. -/
def U₀₃ {n : ℕ} : Circ (n + 4) := tseq [SW₀₁, SW₁₂, U₂₃, SW₁₂, SW₀₁]

/-- `V` on wires `0, 1, 2` (Definition 3.2): it acts by
`ω^{x₀ ⊕ x₁ ⊕ x₂}`. -/
def V₀₁₂ {n : ℕ} : Circ (n + 3) := tseq [CX₂₁, CX₁₀, T₀, CX₁₀, CX₂₁]
/-- `V` on wires `1, 2, 3`. -/
def V₁₂₃ {n : ℕ} : Circ (n + 4) := shift V₀₁₂
/-- `V` on wires `0, 2, 3`. -/
def V₀₂₃ {n : ℕ} : Circ (n + 4) := tseq [SW₀₁, V₁₂₃, SW₀₁]
/-- `V` on wires `0, 1, 3`. -/
def V₀₁₃ {n : ℕ} : Circ (n + 4) := tseq [SW₁₂, SW₀₁, V₁₂₃, SW₀₁, SW₁₂]

/-! ### The relations -/

/-- The relations of Figure 1, each on the wires it is drawn on, together
with the laws of the symmetry assumed in §2.  `Rel k w v`: `w = v` on `k`
wires. -/
inductive Rel : CRel Gate
  /-- `R₁`: `X² = 1`. -/
  | R1 : Rel 1 (tseq [X₀, X₀]) 1
  /-- `R₂`: `X` on the target commutes with `CNOT`. -/
  | R2 : Rel 2 (tseq [CX₁₀, X₀, CX₁₀]) X₀
  /-- `R₃`: `X` on the control is copied to the target. -/
  | R3 : Rel 2 (tseq [CX₁₀, X₁, CX₁₀]) (tseq [X₁, X₀])
  /-- `R₄`: `CNOT² = 1`. -/
  | R4 : Rel 2 (tseq [CX₁₀, CX₁₀]) 1
  /-- `R₅`: `SWAP` from three `CNOT`s. -/
  | R5 : Rel 2 SW₀₁ (tseq [CX₁₀, SW₀₁, CX₁₀, SW₀₁, CX₁₀])
  /-- `R₆`: a `CNOT` on non-adjacent wires. -/
  | R6 : Rel 3 CX₂₀ (tseq [CX₁₀, CX₂₁, CX₁₀, CX₂₁])
  /-- `R₇`: `T⁸ = 1`. -/
  | R7 : Rel 1 (T₀ ^ 8) 1
  /-- `R₈`: `U⁴ = T⁴ ⊗ T⁴`. -/
  | R8 : Rel 2 (U₀₁ ^ 4) (tseq [T₀ ^ 4, T₁ ^ 4])
  /-- `R₉`: `V² = T⁶ ⊗ T⁶ ⊗ T⁶` followed by `U²` on each pair of wires. -/
  | R9 : Rel 3 (V₀₁₂ ^ 2)
      (tseq [T₀ ^ 6, T₁ ^ 6, T₂ ^ 6, U₁₂ ^ 2, U₀₂ ^ 2, U₀₁ ^ 2])
  /-- `R₁₀`: `ω⁸ = 1`. -/
  | R10 : Rel 0 (om ^ 8) 1
  /-- `R₁₁`: `X T X = ω T⁷`. -/
  | R11 : Rel 1 (tseq [X₀, T₀, X₀]) (tseq [om, T₀ ^ 7])
  /-- `R₁₂`: `T` on the control commutes with `CNOT`. -/
  | R12 : Rel 2 (tseq [CX₁₀, T₁, CX₁₀]) T₁
  /-- `R₁₃`: the four-wire parity phase, `CNOT` and `V`, as `T⁵` on each
  wire, `U³` on each pair and `V` on each triple of wires. -/
  | R13 : Rel 4 (tseq [CX₃₂, V₀₁₂, CX₃₂])
      (tseq [T₀ ^ 5, T₁ ^ 5, T₂ ^ 5, T₃ ^ 5,
        U₂₃ ^ 3, U₁₃ ^ 3, U₀₃ ^ 3, U₁₂ ^ 3, U₀₂ ^ 3, U₀₁ ^ 3,
        V₁₂₃, V₀₂₃, V₀₁₃, V₀₁₂])
  /-- §2: the symmetry is self-inverse. -/
  | swap_swap : Rel 2 (tseq [SW₀₁, SW₀₁]) 1
  /-- §2: naturality of the symmetry for a one-wire gate. -/
  | swap_nat1 (g : Gate 1) : Rel 2 (tseq [g1 g, SW₀₁]) (tseq [SW₀₁, shift (g1 g)])
  /-- §2: naturality of the symmetry for a two-wire gate (for `g = SWAP`,
  the Yang–Baxter equation): the gate on wires `0, 1`, then the wires
  `0, 1, 2` carried to `1, 2, 0`, is the same permutation followed by the
  gate on wires `1, 2`. -/
  | swap_nat2 (g : Gate 2) :
      Rel 3 (tseq [g2 g, SW₁₂, SW₀₁]) (tseq [SW₁₂, SW₀₁, shift (g2 g)])

/-- The theory of CNOT-dihedral circuits on `n` wires: the relations on the
bottom wires of every circuit, with the structural rules. -/
abbrev Theory : CRel Gate := Lift (Padded Rel)

end QCert.CNOTDihedral
