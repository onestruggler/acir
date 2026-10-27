/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit Clifford+T circuits: the matrices of the generators

Section 2 of Bian–Selinger (arXiv:2204.02217):

  ω = e^{iπ/4},  H = (1/√2) [[1, 1], [1, -1]],  S = diag(1, i),
  T = diag(1, ω),  CZ = diag(1, 1, 1, -1),

with `A₀ = A ⊗ I`, `A₁ = I ⊗ A` and the scalar `ω` read as `ω I`.  A
4 × 4 matrix is indexed by `Fin 4`, the basis state `|q₀ q₁⟩` at index
`2 q₀ + q₁` (qubit 0, the top wire, is the most significant digit), the
index set of Greylyn's two-level matrices in Section 4.1.

The matrices are written over ℚ(ω) (`QOmega`) and read in `ℂ` through
`QOmega.toC`; `sem` is the semantics in the unitary group `U(4)`, and
`semU` the same in `U₄(ℤ[1/√2, i])`.
-/
import QCert.CliffordT2.Syntax
import QCert.CliffordT2.Exact
import QCert.Matrix.Rings

namespace QCert.CliffordT2

open Matrix

/-- `1/√2 ∈ ℚ(ω)`. -/
abbrev s : QOmega := QOmega.invSqrt2
/-- `i ∈ ℚ(ω)`. -/
abbrev iQ : QOmega := QOmega.I
/-- `ω ∈ ℚ(ω)`. -/
abbrev ωQ : QOmega := Quartic.X

/-- `H = (1/√2) [[1, 1], [1, -1]]`. -/
def Hm : Matrix (Fin 2) (Fin 2) QOmega := !![s, s; s, -s]
/-- `S = diag(1, i)`. -/
def Sm : Matrix (Fin 2) (Fin 2) QOmega := !![1, 0; 0, iQ]
/-- `T = diag(1, ω)`. -/
def Tm : Matrix (Fin 2) (Fin 2) QOmega := !![1, 0; 0, ωQ]
/-- `CZ = diag(1, 1, 1, -1)`. -/
def CZm : Matrix (Fin 4) (Fin 4) QOmega :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- `A ⊗ I`, the gate `A` on qubit 0. -/
def on0 (A : Matrix (Fin 2) (Fin 2) QOmega) : Matrix (Fin 4) (Fin 4) QOmega :=
  tensor (m := 2) (n := 2) A 1
/-- `I ⊗ A`, the gate `A` on qubit 1. -/
def on1 (A : Matrix (Fin 2) (Fin 2) QOmega) : Matrix (Fin 4) (Fin 4) QOmega :=
  tensor (m := 2) (n := 2) 1 A

/-- The matrices of the generators over ℚ(ω). -/
def matQ : Gen → Matrix (Fin 4) (Fin 4) QOmega
  | .ω => ωQ • 1
  | .H₀ => on0 Hm
  | .H₁ => on1 Hm
  | .S₀ => on0 Sm
  | .S₁ => on1 Sm
  | .T₀ => on0 Tm
  | .T₁ => on1 Tm
  | .CZ => CZm

theorem matQ_unitary : ∀ x : Gen, matQ x * dagQ (matQ x) = 1 := by
  decide +kernel

/-- The semantics of the generators in `U(4)`. -/
noncomputable def sem (x : Gen) : unitaryGroup (Fin 4) ℂ :=
  unitaryQ (matQ x) (matQ_unitary x)

/-- The entries of the generators: `0, ±1, ±1/√2, i, ω`. -/
def entries : List QOmega := [0, 1, -1, s, -s, iQ, ωQ]

theorem matQ_entries : ∀ (x : Gen) (i j : Fin 4), matQ x i j ∈ entries := by
  decide +kernel

theorem entries_mem : ∀ y ∈ entries, QOmega.toC y ∈ ZInvSqrt2I := by
  have hs : QOmega.toC s ∈ ZInvSqrt2I := by
    rw [QOmega.toC_invSqrt2]; exact Subring.subset_closure (by simp)
  have hi : QOmega.toC iQ ∈ ZInvSqrt2I := by
    rw [QOmega.toC_I]; exact Subring.subset_closure (by simp)
  intro y hy
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_zero]; exact Subring.zero_mem _
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_neg, map_one]; exact Subring.neg_mem _ (Subring.one_mem _)
  · exact hs
  · rw [map_neg]; exact Subring.neg_mem _ hs
  · exact hi
  · rw [QOmega.toC_X]
    have : ω = QOmega.toC s * (1 + QOmega.toC iQ) := by
      rw [QOmega.toC_invSqrt2, QOmega.toC_I]; rfl
    rw [this]
    exact Subring.mul_mem _ hs (Subring.add_mem _ (Subring.one_mem _) hi)

theorem sem_mem (x : Gen) : sem x ∈ U_ZInvSqrt2I 4 := by
  intro i j
  exact entries_mem _ (matQ_entries x i j)

/-- The semantics of the generators in `U₄(ℤ[1/√2, i])`. -/
noncomputable def semU (x : Gen) : U_ZInvSqrt2I 4 := ⟨sem x, sem_mem x⟩

end QCert.CliffordT2
