/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): gates and relations

P. Selinger, *Generators and relations for n-qubit Clifford operators*,
Logical Methods in Computer Science 11(2:10), 2015, arXiv:1310.6813.

The generators are `ω = e^{iπ/4}`, `H`, `S` and the controlled-`Z` gate
`Z_c` on adjacent qubits (equation (1.1)), and the relations are C1–C15 of
Figure 8, a presentation as a strict spatial monoidal groupoid (§2): the
bifunctorial and spatial laws are our structural rules.

**Wires.**  The diagrams of Figure 8 are drawn with wires at heights
`y = 0, 1, 2`; the wire at height `0` (the bottom wire) is our wire `0`.
(The paper numbers qubits from the top, so its last qubit is our wire `0`.)
`Z_c` is symmetric in its two qubits.

**Order.**  Circuits are words in operator order (`w * v` applies `v`
first).  The one-qubit equations C2–C4 are printed as matrix products and are
transcribed as such; the circuit equations C5–C15 are written in the time
order of the diagrams with `tseq [c₁, c₂, …]` (`c₁` applied first).
-/
import QCert.Circuit.Basic

namespace QCert.SelingerClifford

open Circuit

/-- The gates (equation (1.1)). -/
inductive Gate : ℕ → Type
  /-- The scalar `ω = e^{iπ/4}`. -/
  | ω : Gate 0
  /-- The Hadamard gate. -/
  | H : Gate 1
  /-- The phase gate `S = diag(1, i)`. -/
  | S : Gate 1
  /-- The controlled-`Z` gate `Z_c`. -/
  | CZ : Gate 2
  deriving DecidableEq

/-- Clifford circuits. -/
abbrev Circ (n : ℕ) := Circuit Gate n

/-- A circuit written in time order: the first circuit of the list is
applied first. -/
def tseq {n : ℕ} : List (Circ n) → Circ n
  | [] => 1
  | c :: cs => tseq cs * c

/-! ### Gates on given wires -/

/-- The scalar `ω`. -/
abbrev om {n : ℕ} : Circ n := g0 Gate.ω
/-- `H` on wire `0`. -/
abbrev H₀ {n : ℕ} : Circ (n + 1) := g1 Gate.H
/-- `H` on wire `1`. -/
abbrev H₁ {n : ℕ} : Circ (n + 2) := shift H₀
/-- `H` on wire `2`. -/
abbrev H₂ {n : ℕ} : Circ (n + 3) := shift H₁
/-- `S` on wire `0`. -/
abbrev S₀ {n : ℕ} : Circ (n + 1) := g1 Gate.S
/-- `S` on wire `1`. -/
abbrev S₁ {n : ℕ} : Circ (n + 2) := shift S₀
/-- `Z_c` on wires `0, 1`. -/
abbrev CZ₀₁ {n : ℕ} : Circ (n + 2) := g2 Gate.CZ
/-- `Z_c` on wires `1, 2`. -/
abbrev CZ₁₂ {n : ℕ} : Circ (n + 3) := shift CZ₀₁

/-! ### The relations -/

/-- The relations C1–C15 of Figure 8, each on the number of qubits of its
part (a)–(d) of the figure.  `Rel k w v`: `w = v` on `k` wires. -/
inductive Rel : CRel Gate
  /-- C1: `ω⁸ = 1`. -/
  | C1 : Rel 0 (om ^ 8) 1
  /-- C2: `H² = 1`. -/
  | C2 : Rel 1 (H₀ * H₀) 1
  /-- C3: `S⁴ = 1`. -/
  | C3 : Rel 1 (S₀ * S₀ * S₀ * S₀) 1
  /-- C4: `SHSHSH = ω`. -/
  | C4 : Rel 1 (S₀ * H₀ * S₀ * H₀ * S₀ * H₀) om
  /-- C5: `Z_c² = 1`. -/
  | C5 : Rel 2 (tseq [CZ₀₁, CZ₀₁]) 1
  /-- C6: `S` on the upper wire commutes with `Z_c`. -/
  | C6 : Rel 2 (tseq [S₁, CZ₀₁]) (tseq [CZ₀₁, S₁])
  /-- C7: `S` on the lower wire commutes with `Z_c`. -/
  | C7 : Rel 2 (tseq [S₀, CZ₀₁]) (tseq [CZ₀₁, S₀])
  /-- C8: `HSSH` on the upper wire, then `Z_c`. -/
  | C8 : Rel 2 (tseq [H₁, S₁, S₁, H₁, CZ₀₁])
      (tseq [CZ₀₁, S₀, S₀, H₁, S₁, S₁, H₁])
  /-- C9: `HSSH` on the lower wire, then `Z_c`. -/
  | C9 : Rel 2 (tseq [H₀, S₀, S₀, H₀, CZ₀₁])
      (tseq [CZ₀₁, S₁, S₁, H₀, S₀, S₀, H₀])
  /-- C10: `Z_c`, `H` on the upper wire, `Z_c`; the right-hand side carries
  the scalar `ω⁻¹ = ω⁷`. -/
  | C10 : Rel 2 (tseq [CZ₀₁, H₁, CZ₀₁])
      (tseq [S₁, H₁, CZ₀₁, S₀, S₁, H₁, S₁, om ^ 7])
  /-- C11: `Z_c`, `H` on the lower wire, `Z_c`; the right-hand side carries
  the scalar `ω⁻¹ = ω⁷`. -/
  | C11 : Rel 2 (tseq [CZ₀₁, H₀, CZ₀₁])
      (tseq [S₀, H₀, CZ₀₁, S₁, S₀, H₀, S₀, om ^ 7])
  /-- C12: `Z_c` on wires `0, 1` and on wires `1, 2` commute. -/
  | C12 : Rel 3 (tseq [CZ₀₁, CZ₁₂]) (tseq [CZ₁₂, CZ₀₁])
  /-- C13. -/
  | C13 : Rel 3
      (tseq [CZ₁₂, H₂, H₁, CZ₁₂, H₁, H₀, CZ₀₁, H₁, H₀, CZ₁₂, H₂, H₁, CZ₁₂])
      (tseq [CZ₀₁, H₀, H₁, CZ₀₁, H₁, H₂, CZ₁₂, H₁, H₂, CZ₀₁, H₀, H₁, CZ₀₁])
  /-- C14. -/
  | C14 : Rel 3
      (tseq [CZ₁₂, H₂, H₁, CZ₁₂, H₂, H₁, CZ₀₁, CZ₁₂, H₂, H₁, CZ₁₂, H₂, H₁, CZ₀₁,
        CZ₁₂, H₂, H₁, CZ₁₂, H₁, H₂, CZ₀₁]) 1
  /-- C15. -/
  | C15 : Rel 3
      (tseq [CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₁₂, CZ₀₁, H₀, H₁, CZ₀₁, H₀, H₁, CZ₁₂,
        CZ₀₁, H₀, H₁, CZ₀₁, H₁, H₀, CZ₁₂]) 1

/-- The theory of Clifford circuits on `n` wires: the relations on the
bottom wires of every circuit, with the structural rules. -/
abbrev Theory : CRel Gate := Lift (Padded Rel)

end QCert.SelingerClifford
