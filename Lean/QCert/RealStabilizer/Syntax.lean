/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: gates and relations

S. Makary, N. J. Ross and P. Selinger, *Generators and relations for real
stabilizer operators*, QPL 2021 (EPTCS 343), arXiv:2109.05655.

The generators are the scalar `-1` and the gates `H`, `Z` and `CZ` (§2),
and the relations are the reduced relations R1–R16 of Figure 1
(Definition 5.6), a presentation as a monoidal groupoid: the bifunctorial
and spatial laws are our structural rules.

**Wires.**  The diagrams of Figure 1 are drawn with wires at heights
`y = 0, 1.6, 3.2`; the wire at height `0` (the bottom wire) is our wire `0`,
the one at `1.6` wire `1`, the one at `3.2` wire `2`.  `CZ` is symmetric in
its two qubits.

**Order.**  Circuits are words in operator order (`w * v` applies `v`
first); `tseq [c₁, c₂, …]` writes a circuit in the time order of a diagram,
`c₁` first.  Gates drawn at the same horizontal position act on disjoint
wires and are listed bottom wire first.
-/
import QCert.Circuit.Basic

namespace QCert.RealStabilizer

open Circuit

/-- The gates. -/
inductive Gate : ℕ → Type
  /-- The scalar `-1`. -/
  | neg : Gate 0
  /-- The Hadamard gate. -/
  | H : Gate 1
  /-- The Pauli `Z` gate. -/
  | Z : Gate 1
  /-- The controlled-`Z` gate. -/
  | CZ : Gate 2
  deriving DecidableEq

/-- Real stabilizer circuits. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- A circuit written in time order: the first circuit of the list is
applied first. -/
def tseq {n : ℕ} : List (Circ n) → Circ n
  | [] => 1
  | c :: cs => tseq cs * c

/-! ### Gates on given wires -/

/-- The scalar `-1`. -/
abbrev mone {n : ℕ} : Circ n := g0 Gate.neg
/-- `H` on wire `0`. -/
abbrev H₀ {n : ℕ} : Circ (n + 1) := g1 Gate.H
/-- `H` on wire `1`. -/
abbrev H₁ {n : ℕ} : Circ (n + 2) := shift H₀
/-- `H` on wire `2`. -/
abbrev H₂ {n : ℕ} : Circ (n + 3) := shift H₁
/-- `Z` on wire `0`. -/
abbrev Z₀ {n : ℕ} : Circ (n + 1) := g1 Gate.Z
/-- `Z` on wire `1`. -/
abbrev Z₁ {n : ℕ} : Circ (n + 2) := shift Z₀
/-- `CZ` on wires `0, 1`. -/
abbrev CZ₀₁ {n : ℕ} : Circ (n + 2) := g2 Gate.CZ
/-- `CZ` on wires `1, 2`. -/
abbrev CZ₁₂ {n : ℕ} : Circ (n + 3) := shift CZ₀₁

/-! ### The relations -/

/-- The reduced relations R1–R16 of Figure 1 (Definition 5.6), each on the
wires it is drawn on.  `Rel k w v`: `w = v` on `k` wires. -/
inductive Rel : CRel Gate
  /-- R1: `(-1)² = 1`. -/
  | R1 : Rel 0 (tseq [mone, mone]) 1
  /-- R2: `Z² = 1`. -/
  | R2 : Rel 1 (tseq [Z₀, Z₀]) 1
  /-- R3: `H² = 1`. -/
  | R3 : Rel 1 (tseq [H₀, H₀]) 1
  /-- R4: `(Z H)⁴ = -1`. -/
  | R4 : Rel 1 (tseq [Z₀, H₀, Z₀, H₀, Z₀, H₀, Z₀, H₀]) mone
  /-- R5: `CZ² = 1`. -/
  | R5 : Rel 2 (tseq [CZ₀₁, CZ₀₁]) 1
  /-- R6: `Z` on the upper wire commutes with `CZ`. -/
  | R6 : Rel 2 (tseq [Z₁, CZ₀₁]) (tseq [CZ₀₁, Z₁])
  /-- R7: `Z` on the lower wire commutes with `CZ`. -/
  | R7 : Rel 2 (tseq [Z₀, CZ₀₁]) (tseq [CZ₀₁, Z₀])
  /-- R8: `HZH` on the upper wire, then `CZ`. -/
  | R8 : Rel 2 (tseq [H₁, Z₁, H₁, CZ₀₁]) (tseq [CZ₀₁, H₁, Z₀, Z₁, H₁])
  /-- R9: `HZH` on the lower wire, then `CZ`. -/
  | R9 : Rel 2 (tseq [H₀, Z₀, H₀, CZ₀₁]) (tseq [CZ₀₁, H₀, Z₀, Z₁, H₀])
  /-- R10. -/
  | R10 : Rel 2 (tseq [H₁, CZ₀₁, H₁, CZ₀₁]) (tseq [CZ₀₁, H₁, CZ₀₁, Z₀, H₁])
  /-- R11. -/
  | R11 : Rel 2 (tseq [H₀, CZ₀₁, H₀, CZ₀₁]) (tseq [CZ₀₁, H₀, CZ₀₁, H₀, Z₁])
  /-- R12. -/
  | R12 : Rel 2 (tseq [H₀, CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₀₁])
      (tseq [CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₀₁, H₁])
  /-- R13: `CZ` on wires `1, 2` and on wires `0, 1` commute. -/
  | R13 : Rel 3 (tseq [CZ₁₂, CZ₀₁]) (tseq [CZ₀₁, CZ₁₂])
  /-- R14. -/
  | R14 : Rel 3
      (tseq [H₀, CZ₀₁, H₀, H₁, CZ₀₁, H₁, CZ₁₂, H₁, CZ₀₁, H₀, H₁, CZ₀₁, H₀])
      (tseq [H₂, CZ₁₂, H₁, H₂, CZ₁₂, H₁, CZ₀₁, H₁, CZ₁₂, H₁, H₂, CZ₁₂, H₂])
  /-- R15. -/
  | R15 : Rel 3
      (tseq [CZ₁₂, H₁, H₂, CZ₁₂, H₁, H₂, CZ₀₁, CZ₁₂, H₁, H₂, CZ₁₂, H₁, H₂, CZ₀₁])
      (tseq [CZ₀₁, H₁, H₂, CZ₁₂, H₁, H₂, CZ₁₂])
  /-- R16. -/
  | R16 : Rel 3
      (tseq [CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₁₂, CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₁₂])
      (tseq [CZ₁₂, H₀, H₁, CZ₀₁, H₀, H₁, CZ₀₁])

/-- The theory of real stabilizer circuits on `n` wires: the relations on
the bottom wires of every circuit, with the structural rules. -/
abbrev Theory : CRel Gate := Lift (Padded Rel)

end QCert.RealStabilizer
