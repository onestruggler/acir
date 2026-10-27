/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit Clifford+T circuits: generators and relations

Bian and Selinger, *Generators and relations for 2-qubit Clifford+T
operators* (QPL 2022, arXiv:2204.02217).  Theorem 2.1 presents the
two-qubit Clifford+T group by the generators

  𝒳 = {ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ}

and the relations (C1)–(C20) of Figure 1, with the abbreviations of
Figure 2.  Words are written in the order of matrix multiplication (the
paper: "We write circuits in the same order as matrix multiplication"),
so `w * v` applies `v` first.  The qubits are numbered from the top:
`A₀ = A ⊗ I` acts on qubit 0 (top wire), `A₁ = I ⊗ A` on qubit 1 (bottom
wire).  In the paper's circuit pictures the top wire is drawn at height 1
and the bottom wire at height 0.

The relations are transcribed from Figure 1; where Figure 1 draws two
gates on different qubits at the same horizontal position, the order
chosen is the one of the authors' statement in their accompanying code
(`Generator.agda`, in the arXiv ancillary files).
-/
import QCert.Presentation
import Mathlib.Tactic.DeriveFintype

namespace QCert.CliffordT2

/-- The generators 𝒳 of Theorem 2.1. -/
inductive Gen : Type
  | ω | H₀ | H₁ | S₀ | S₁ | T₀ | T₁ | CZ
  deriving DecidableEq, Fintype, Repr

/-- The one-qubit gate names of relation (C2), `A, B ∈ {H, S, T}`. -/
inductive Local : Type
  | H | S | T
  deriving DecidableEq, Fintype, Repr

/-- The generator `A_i`: the one-qubit gate `A` on qubit `i`. -/
def Local.on : Local → Fin 2 → Gen
  | .H, 0 => .H₀
  | .H, 1 => .H₁
  | .S, 0 => .S₀
  | .S, 1 => .S₁
  | .T, 0 => .T₀
  | .T, 1 => .T₁

namespace W

/-! Generators as one-letter words, and the abbreviations of Figure 2. -/

/-- The letter `g`. -/
abbrev g (x : Gen) : Word Gen := FreeMonoid.of x

abbrev ω : Word Gen := g .ω
abbrev CZ : Word Gen := g .CZ
/-- `H_i`. -/
abbrev H (i : Fin 2) : Word Gen := g (Local.H.on i)
/-- `S_i`. -/
abbrev S (i : Fin 2) : Word Gen := g (Local.S.on i)
/-- `T_i`. -/
abbrev T (i : Fin 2) : Word Gen := g (Local.T.on i)

/-- `ω⁻¹ = ω⁷`. -/
def ωinv : Word Gen := ω ^ 7
/-- `T† = T⁷` (Figure 2). -/
def Tdg (i : Fin 2) : Word Gen := T i ^ 7
/-- `S† = S³` (Figure 2). -/
def Sdg (i : Fin 2) : Word Gen := S i ^ 3
/-- `X_i = H_i S_i S_i H_i` (the `X` of Figure 1, (C10), (C11), (C15)). -/
def X (i : Fin 2) : Word Gen := H i * S i * S i * H i
/-- The controlled not with target qubit `i` (control the other qubit):
`H_i CZ H_i` (Figure 2, first abbreviation). -/
def CX (i : Fin 2) : Word Gen := H i * CZ * H i
/-- The controlled not with a white control (control on `|0⟩`), target
qubit `i`: `CX_i X_i` (Figure 2, second abbreviation). -/
def CXw (i : Fin 2) : Word Gen := CX i * X i
/-- The controlled Hadamard with target qubit `i`:
`S_i H_i T_i CX_i T_i† H_i S_i†` (Figure 2, third abbreviation). -/
def CH (i : Fin 2) : Word Gen := S i * H i * T i * CX i * Tdg i * H i * Sdg i
/-- The controlled Hadamard with a white control, target qubit `i`:
`CH_i H_i` (Figure 2, last abbreviation). -/
def CHw (i : Fin 2) : Word Gen := CH i * H i

end W

open W

/-- The relations 𝒮 of Figure 1 (C1)–(C20).  Constructors indexed by
`i : Fin 2` stand for the two relations `i = 0, 1` of the figure ("Here
i ∈ {0, 1}"). -/
inductive Rel : WRel Gen
  /-- (C1) `ω A = A ω`, `A ∈ {H_i, S_i, T_i, CZ}`. -/
  | c1 (A : Gen) (hA : A ≠ .ω) : Rel (ω * g A) (g A * ω)
  /-- (C2) `A₀ B₁ = B₁ A₀`, `A, B ∈ {H, S, T}`. -/
  | c2 (A B : Local) : Rel (g (A.on 0) * g (B.on 1)) (g (B.on 1) * g (A.on 0))
  /-- (C3) `ω⁸ = ε`. -/
  | c3 : Rel (ω ^ 8) 1
  /-- (C4) `H_i² = ε`. -/
  | c4 (i : Fin 2) : Rel (H i ^ 2) 1
  /-- (C5) `S_i⁴ = ε`. -/
  | c5 (i : Fin 2) : Rel (S i ^ 4) 1
  /-- (C6) `(S_i H_i)³ = ω`. -/
  | c6 (i : Fin 2) : Rel ((S i * H i) ^ 3) ω
  /-- (C7) `CZ² = ε`. -/
  | c7 : Rel (CZ ^ 2) 1
  /-- (C8) `S₀ CZ = CZ S₀`. -/
  | c8 : Rel (S 0 * CZ) (CZ * S 0)
  /-- (C9) `S₁ CZ = CZ S₁`. -/
  | c9 : Rel (S 1 * CZ) (CZ * S 1)
  /-- (C10) `H₀ S₀ S₀ H₀ CZ = CZ S₁ S₁ H₀ S₀ S₀ H₀`. -/
  | c10 : Rel (X 0 * CZ) (CZ * S 1 * S 1 * X 0)
  /-- (C11) `H₁ S₁ S₁ H₁ CZ = CZ S₀ S₀ H₁ S₁ S₁ H₁`. -/
  | c11 : Rel (X 1 * CZ) (CZ * S 0 * S 0 * X 1)
  /-- (C12) `CZ H₀ CZ = S₀ H₀ CZ S₀ H₀ S₀ S₁ ω⁻¹`. -/
  | c12 : Rel (CZ * H 0 * CZ) (S 0 * H 0 * CZ * S 0 * H 0 * S 0 * S 1 * ωinv)
  /-- (C13) `CZ H₁ CZ = S₁ H₁ CZ S₁ H₁ S₁ S₀ ω⁻¹`. -/
  | c13 : Rel (CZ * H 1 * CZ) (S 1 * H 1 * CZ * S 1 * H 1 * S 1 * S 0 * ωinv)
  /-- (C14) `T_i² = S_i`. -/
  | c14 (i : Fin 2) : Rel (T i ^ 2) (S i)
  /-- (C15) `(T_i H_i S_i S_i H_i)² = ω`. -/
  | c15 (i : Fin 2) : Rel ((T i * X i) ^ 2) ω
  /-- (C16) `T₀ CZ = CZ T₀`. -/
  | c16 : Rel (T 0 * CZ) (CZ * T 0)
  /-- (C17) `H₁ CZ H₀ H₁ CZ H₀ T₀ = T₁ H₁ CZ H₀ H₁ CZ H₀`. -/
  | c17 : Rel (H 1 * CZ * H 0 * H 1 * CZ * H 0 * T 0) (T 1 * H 1 * CZ * H 0 * H 1 * CZ * H 0)
  /-- (C18) `CX₁ T₁ H₁ T₁† (CX₁ X₁) T₁ H₁ T₁† = T₁ H₁ T₁† (CX₁ X₁) T₁ H₁ T₁† CX₁`,
  the first "non-obvious" relation. -/
  | c18 : Rel (CX 1 * T 1 * H 1 * Tdg 1 * CXw 1 * T 1 * H 1 * Tdg 1)
      (T 1 * H 1 * Tdg 1 * CXw 1 * T 1 * H 1 * Tdg 1 * CX 1)
  /-- (C19) `CX₁ T₁ H₁ T₁ H₁ T₁† (CX₁ X₁) T₁ H₁ T₁† H₁ T₁† =
  T₁ H₁ T₁ H₁ T₁† (CX₁ X₁) T₁ H₁ T₁† H₁ T₁† CX₁`. -/
  | c19 : Rel (CX 1 * T 1 * H 1 * T 1 * H 1 * Tdg 1 * CXw 1 * T 1 * H 1 * Tdg 1 * H 1 * Tdg 1)
      (T 1 * H 1 * T 1 * H 1 * Tdg 1 * CXw 1 * T 1 * H 1 * Tdg 1 * H 1 * Tdg 1 * CX 1)
  /-- (C20) `(CH₁ H₁) T₁ CH₁ (CH₀ H₀) T₀ CH₀ = (CH₀ H₀) T₀ CH₀ (CH₁ H₁) T₁ CH₁`. -/
  | c20 : Rel (CHw 1 * T 1 * CH 1 * CHw 0 * T 0 * CH 0)
      (CHw 0 * T 0 * CH 0 * CHw 1 * T 1 * CH 1)

end QCert.CliffordT2
