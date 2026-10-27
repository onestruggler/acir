/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS circuits: generators and relations

Bian and Selinger, *Generators and relations for 3-qubit Clifford+CS
operators* (QPL 2023, arXiv:2306.08530).  Theorem 3.1 presents the
three-qubit Clifford+CS group by the generators

  𝒳 = {i, K₀, K₁, K₂, S₀, S₁, S₂, CS₀₁, CS₁₂}

and the relations 𝒮_𝒳 of Figure 2: (C1)–(C17), where each relation of
part (b) stands for three relations (one per qubit) and each relation of
part (c) for two (one per pair of adjacent qubits), together with the
monoidal relations of part (e): "the scalar `i` commutes with everything,
and non-overlapping gates commute".

Words are written in the order of matrix multiplication ("from right to
left"), so `w * v` applies `v` first.  The qubits are numbered from the
top: `K₀ = K ⊗ I ⊗ I`, `K₁ = I ⊗ K ⊗ I`, `K₂ = I ⊗ I ⊗ K`,
`CS₀₁ = CS ⊗ I`, `CS₁₂ = I ⊗ CS`.  In the paper's circuit pictures qubit
`q` is drawn at height `2 - q` (three qubits) and, in the two-qubit
relations of part (c), the upper qubit `j` of the pair `(j, j + 1)` at
height 1 and the lower qubit `j + 1` at height 0.

The derived gates of Section 2.1 (`X = K S S K i` and the controlled not
`K_t CS CS K_t i`, target `t`) and Section 4.1 are abbreviations.  In the
notation `CX_{ct}` of the paper, `c` is the control and `t` the target.
-/
import QCert.Presentation
import Mathlib.Tactic.DeriveFintype

namespace QCert.CliffordCS3

/-- The generators 𝒳 of Theorem 3.1. -/
inductive Gen : Type
  | i | K₀ | K₁ | K₂ | S₀ | S₁ | S₂ | CS₀₁ | CS₁₂
  deriving DecidableEq, Fintype, Repr

/-- The one-qubit gate names. -/
inductive Local : Type
  | K | S
  deriving DecidableEq, Fintype, Repr

/-- The generator `A_q`: the one-qubit gate `A` on qubit `q`. -/
def Local.on : Local → Fin 3 → Gen
  | .K, 0 => .K₀
  | .K, 1 => .K₁
  | .K, 2 => .K₂
  | .S, 0 => .S₀
  | .S, 1 => .S₁
  | .S, 2 => .S₂

/-- `CS_{j,j+1}` for the pair of adjacent qubits `(j, j + 1)`, `j ∈ {0, 1}`. -/
def csOn : Fin 2 → Gen
  | 0 => .CS₀₁
  | 1 => .CS₁₂

namespace W

/-! Generators as one-letter words, and the abbreviations of the paper. -/

/-- The letter `x`. -/
abbrev g (x : Gen) : Word Gen := FreeMonoid.of x

/-- The scalar `i`. -/
abbrev I : Word Gen := g .i
/-- `K_q`. -/
abbrev K (q : Fin 3) : Word Gen := g (Local.K.on q)
/-- `S_q`. -/
abbrev S (q : Fin 3) : Word Gen := g (Local.S.on q)
abbrev CS01 : Word Gen := g .CS₀₁
abbrev CS12 : Word Gen := g .CS₁₂
/-- `CS_{j,j+1}`. -/
abbrev CS (j : Fin 2) : Word Gen := g (csOn j)

/-- `X_q = K_q S_q S_q K_q i` (Section 2.1). -/
def X (q : Fin 3) : Word Gen := K q * S q * S q * K q * I

/-- The controlled not with control `c` and target `t` on adjacent qubits
sharing the gate `CS`: `K_t CS CS K_t i` (Section 2.1, and the first two
notations of Section 4.1). -/
def CX (cs : Word Gen) (t : Fin 3) : Word Gen := K t * cs * cs * K t * I

/-- `CX₀₁`: control qubit 0, target qubit 1. -/
def CX01 : Word Gen := CX CS01 1
/-- `CX₁₀`: control qubit 1, target qubit 0. -/
def CX10 : Word Gen := CX CS01 0
/-- `CX₁₂`: control qubit 1, target qubit 2. -/
def CX12 : Word Gen := CX CS12 2
/-- `CX₂₁`: control qubit 2, target qubit 1. -/
def CX21 : Word Gen := CX CS12 1

end W

open W

/-- The relations 𝒮_𝒳 of Figure 2.  Constructors indexed by a qubit
`q : Fin 3` stand for the three relations of part (b), constructors
indexed by `j : Fin 2` for the two relations of part (c) on the pair of
adjacent qubits `(j, j + 1)`; `Local.on _ (Fin.castSucc j)` is the gate on
the upper qubit `j` of the pair and `Local.on _ (Fin.succ j)` the gate on
the lower qubit `j + 1`. -/
inductive Rel : WRel Gen
  /-- (C1) `i⁴ = ε`. -/
  | c1 : Rel (I ^ 4) 1
  /-- (C2) `K² = i³`. -/
  | c2 (q : Fin 3) : Rel (K q ^ 2) (I ^ 3)
  /-- (C3) `S⁴ = ε`. -/
  | c3 (q : Fin 3) : Rel (S q ^ 4) 1
  /-- (C4) `SKSKSK = i³`. -/
  | c4 (q : Fin 3) : Rel ((S q * K q) ^ 3) (I ^ 3)
  /-- (C5) `CS⁴ = ε`. -/
  | c5 (j : Fin 2) : Rel (CS j ^ 4) 1
  /-- (C6) `S CS = CS S`, `S` on the upper qubit. -/
  | c6 (j : Fin 2) : Rel (S j.castSucc * CS j) (CS j * S j.castSucc)
  /-- (C7) `S CS = CS S`, `S` on the lower qubit. -/
  | c7 (j : Fin 2) : Rel (S j.succ * CS j) (CS j * S j.succ)
  /-- (C8) `X CS = CS CS CS X S`, `X` on the upper qubit and `S` on the
  lower one. -/
  | c8 (j : Fin 2) : Rel (X j.castSucc * CS j) (CS j ^ 3 * X j.castSucc * S j.succ)
  /-- (C9) `X CS = CS CS CS X S`, `X` on the lower qubit and `S` on the
  upper one. -/
  | c9 (j : Fin 2) : Rel (X j.succ * CS j) (CS j ^ 3 * X j.succ * S j.castSucc)
  /-- (C10) `S K CS K CS = CS K CS K S`, `S` and `K` on the upper qubit. -/
  | c10 (j : Fin 2) :
      Rel (S j.castSucc * K j.castSucc * CS j * K j.castSucc * CS j)
        (CS j * K j.castSucc * CS j * K j.castSucc * S j.castSucc)
  /-- (C11) `S K CS K CS = CS K CS K S`, `S` and `K` on the lower qubit. -/
  | c11 (j : Fin 2) :
      Rel (S j.succ * K j.succ * CS j * K j.succ * CS j)
        (CS j * K j.succ * CS j * K j.succ * S j.succ)
  /-- (C12) `CS₁₂ CS₀₁ = CS₀₁ CS₁₂`. -/
  | c12 : Rel (CS12 * CS01) (CS01 * CS12)
  /-- (C13) `CX₁₀ CX₀₁ CS₁₂ CX₀₁ CX₁₀ = CX₁₂ CX₂₁ CS₀₁ CX₂₁ CX₁₂`. -/
  | c13 : Rel (CX10 * CX01 * CS12 * CX01 * CX10) (CX12 * CX21 * CS01 * CX21 * CX12)
  /-- (C14) `CS₁₂ CX₀₁ CS₁₂ CS₁₂ CS₁₂ CX₀₁ = CS₀₁ CX₂₁ CS₀₁ CS₀₁ CS₀₁ CX₂₁`. -/
  | c14 : Rel (CS12 * CX01 * CS12 ^ 3 * CX01) (CS01 * CX21 * CS01 ^ 3 * CX21)
  /-- (C15) `CX₁₀ CX₀₁ CS₁₂ CS₁₂ CX₀₁ CX₁₀ = CX₀₁ CS₁₂ CS₁₂ CX₀₁ CS₁₂ CS₁₂`. -/
  | c15 : Rel (CX10 * CX01 * CS12 ^ 2 * CX01 * CX10) (CX01 * CS12 ^ 2 * CX01 * CS12 ^ 2)
  /-- (C16) `CS₁₂ K₁ CS₁₂ K₁ CS₀₁ K₁ CS₀₁ = CS₀₁ K₁ CS₀₁ K₁ CS₁₂ K₁ CS₁₂`. -/
  | c16 : Rel (CS12 * K 1 * CS12 * K 1 * CS01 * K 1 * CS01)
      (CS01 * K 1 * CS01 * K 1 * CS12 * K 1 * CS12)
  /-- (C17) `CS₁₂ K₁ CS₁₂³ K₁ CS₀₁ K₁ CS₁₂ = CS₀₁ K₁ CS₀₁³ K₁ CS₁₂ K₁ CS₀₁`. -/
  | c17 : Rel (CS12 * K 1 * CS12 ^ 3 * K 1 * CS01 * K 1 * CS12)
      (CS01 * K 1 * CS01 ^ 3 * K 1 * CS12 * K 1 * CS01)
  /-- (e) The scalar `i` commutes with every generator. -/
  | comm_i (A : Gen) (hA : A ≠ .i) : Rel (I * g A) (g A * I)
  /-- (e) One-qubit gates on different qubits commute. -/
  | comm_loc (A B : Local) (q r : Fin 3) (hqr : q < r) :
      Rel (g (A.on q) * g (B.on r)) (g (B.on r) * g (A.on q))
  /-- (e) A gate on qubit 0 commutes with `CS₁₂`. -/
  | comm_0_12 (A : Local) : Rel (g (A.on 0) * CS12) (CS12 * g (A.on 0))
  /-- (e) A gate on qubit 2 commutes with `CS₀₁`. -/
  | comm_2_01 (A : Local) : Rel (g (A.on 2) * CS01) (CS01 * g (A.on 2))

end QCert.CliffordCS3
