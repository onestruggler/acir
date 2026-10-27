/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS circuits: the matrices of the generators

Section 2.1 of Bian–Selinger (arXiv:2306.08530):

  i,  K = (1/(1+i)) [[1, 1], [1, -1]],  S = diag(1, i),
  CS = diag(1, 1, 1, i),

with `K₀ = K ⊗ I ⊗ I`, `K₁ = I ⊗ K ⊗ I`, `K₂ = I ⊗ I ⊗ K` (likewise for
`S`), `CS₀₁ = CS ⊗ I`, `CS₁₂ = I ⊗ CS`, and the scalar `i` read as `i I`.
An 8 × 8 matrix is indexed by `Fin 8`, the basis state `|q₀ q₁ q₂⟩` at
index `4 q₀ + 2 q₁ + q₂` (qubit 0, the top wire, is the most significant
digit), the index set of the two-level matrices of Section 2.2.

The matrices are written over ℚ(ω) (`QOmega`, which contains `1/2` and
`i`) and read in `ℂ` through `QOmega.toC`; `sem` is the semantics in the
unitary group `U(8)`, and `semU` the same in `U₈(ℤ[1/2, i])`.
-/
import QCert.CliffordCS3.Syntax
import QCert.CliffordT2.Exact
import QCert.Matrix.Rings

namespace QCert.CliffordCS3

open Matrix

/-- `i ∈ ℚ(ω)`. -/
abbrev iQ : QOmega := QOmega.I
/-- `1/(1+i) = (1 - i)/2 ∈ ℚ(ω)`. -/
def κ : QOmega := ⟨1 / 2, 0, -1 / 2, 0⟩

/-- `κ (1 + i) = 1`: `κ` is `1/(1+i)`. -/
theorem κ_mul : κ * (1 + iQ) = 1 := by decide +kernel

/-- `K = (1/(1+i)) [[1, 1], [1, -1]]`. -/
def Km : Matrix (Fin 2) (Fin 2) QOmega := !![κ, κ; κ, -κ]
/-- `S = diag(1, i)`. -/
def Sm : Matrix (Fin 2) (Fin 2) QOmega := !![1, 0; 0, iQ]
/-- `CS = diag(1, 1, 1, i)`. -/
def CSm : Matrix (Fin 4) (Fin 4) QOmega :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, iQ]

/-- `A ⊗ I ⊗ I`. -/
def on0 (A : Matrix (Fin 2) (Fin 2) QOmega) : Matrix (Fin 8) (Fin 8) QOmega :=
  tensor (m := 2) (n := 4) A 1
/-- `I ⊗ A ⊗ I`. -/
def on1 (A : Matrix (Fin 2) (Fin 2) QOmega) : Matrix (Fin 8) (Fin 8) QOmega :=
  tensor (m := 2) (n := 4) 1 (tensor (m := 2) (n := 2) A 1)
/-- `I ⊗ I ⊗ A`. -/
def on2 (A : Matrix (Fin 2) (Fin 2) QOmega) : Matrix (Fin 8) (Fin 8) QOmega :=
  tensor (m := 4) (n := 2) 1 A

/-- The matrices of the generators over ℚ(ω). -/
def matQ : Gen → Matrix (Fin 8) (Fin 8) QOmega
  | .i => iQ • 1
  | .K₀ => on0 Km
  | .K₁ => on1 Km
  | .K₂ => on2 Km
  | .S₀ => on0 Sm
  | .S₁ => on1 Sm
  | .S₂ => on2 Sm
  | .CS₀₁ => tensor (m := 4) (n := 2) CSm 1
  | .CS₁₂ => tensor (m := 2) (n := 4) 1 CSm

/-- The matrices of the generators written out entry by entry. -/
def matLit : Gen → Matrix (Fin 8) (Fin 8) QOmega
  | .i => !![iQ, 0, 0, 0, 0, 0, 0, 0;
      0, iQ, 0, 0, 0, 0, 0, 0;
      0, 0, iQ, 0, 0, 0, 0, 0;
      0, 0, 0, iQ, 0, 0, 0, 0;
      0, 0, 0, 0, iQ, 0, 0, 0;
      0, 0, 0, 0, 0, iQ, 0, 0;
      0, 0, 0, 0, 0, 0, iQ, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]
  | .K₀ => !![κ, 0, 0, 0, κ, 0, 0, 0;
      0, κ, 0, 0, 0, κ, 0, 0;
      0, 0, κ, 0, 0, 0, κ, 0;
      0, 0, 0, κ, 0, 0, 0, κ;
      κ, 0, 0, 0, -κ, 0, 0, 0;
      0, κ, 0, 0, 0, -κ, 0, 0;
      0, 0, κ, 0, 0, 0, -κ, 0;
      0, 0, 0, κ, 0, 0, 0, -κ]
  | .K₁ => !![κ, 0, κ, 0, 0, 0, 0, 0;
      0, κ, 0, κ, 0, 0, 0, 0;
      κ, 0, -κ, 0, 0, 0, 0, 0;
      0, κ, 0, -κ, 0, 0, 0, 0;
      0, 0, 0, 0, κ, 0, κ, 0;
      0, 0, 0, 0, 0, κ, 0, κ;
      0, 0, 0, 0, κ, 0, -κ, 0;
      0, 0, 0, 0, 0, κ, 0, -κ]
  | .K₂ => !![κ, κ, 0, 0, 0, 0, 0, 0;
      κ, -κ, 0, 0, 0, 0, 0, 0;
      0, 0, κ, κ, 0, 0, 0, 0;
      0, 0, κ, -κ, 0, 0, 0, 0;
      0, 0, 0, 0, κ, κ, 0, 0;
      0, 0, 0, 0, κ, -κ, 0, 0;
      0, 0, 0, 0, 0, 0, κ, κ;
      0, 0, 0, 0, 0, 0, κ, -κ]
  | .S₀ => !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, iQ, 0, 0, 0;
      0, 0, 0, 0, 0, iQ, 0, 0;
      0, 0, 0, 0, 0, 0, iQ, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]
  | .S₁ => !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, iQ, 0, 0, 0, 0, 0;
      0, 0, 0, iQ, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, iQ, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]
  | .S₂ => !![1, 0, 0, 0, 0, 0, 0, 0;
      0, iQ, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, iQ, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, iQ, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]
  | .CS₀₁ => !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, iQ, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]
  | .CS₁₂ => !![1, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, iQ, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, iQ]

theorem matQ_eq_matLit : ∀ x : Gen, matQ x = matLit x := by decide +kernel

theorem matQ_unitary : ∀ x : Gen, matQ x * dagQ (matQ x) = 1 := by
  intro x; rw [matQ_eq_matLit]; revert x; decide +kernel

/-- The semantics of the generators in `U(8)`. -/
noncomputable def sem (x : Gen) : unitaryGroup (Fin 8) ℂ :=
  unitaryQ (matQ x) (matQ_unitary x)

/-- The entries of the generators: `0, ±1, ±1/(1+i), i`. -/
def entries : List QOmega := [0, 1, -1, κ, -κ, iQ]

theorem matQ_entries : ∀ (x : Gen) (i j : Fin 8), matQ x i j ∈ entries := by
  intro x; rw [matQ_eq_matLit]; revert x; decide +kernel

theorem entries_mem : ∀ y ∈ entries, QOmega.toC y ∈ ZHalfI := by
  have hh : (2 : ℂ)⁻¹ ∈ ZHalfI := Subring.subset_closure (by simp)
  have hi : QOmega.toC iQ ∈ ZHalfI := by
    rw [QOmega.toC_I]; exact Subring.subset_closure (by simp)
  have hκ : QOmega.toC κ ∈ ZHalfI := by
    have e : κ = (Quartic.ofRat (1 / 2) : QOmega) * (1 - iQ) := by decide +kernel
    have h2 : QOmega.toC (Quartic.ofRat (1 / 2) : QOmega) = (2 : ℂ)⁻¹ := by
      rw [QOmega.toC, Quartic.lift_ofRat]; push_cast; ring
    rw [e, map_mul, map_sub, map_one, h2]
    exact Subring.mul_mem _ hh (Subring.sub_mem _ (Subring.one_mem _) hi)
  intro y hy
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_zero]; exact Subring.zero_mem _
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_neg, map_one]; exact Subring.neg_mem _ (Subring.one_mem _)
  · exact hκ
  · rw [map_neg]; exact Subring.neg_mem _ hκ
  · exact hi

theorem sem_mem (x : Gen) : sem x ∈ U_ZHalfI 8 := by
  intro i j
  exact entries_mem _ (matQ_entries x i j)

/-- The semantics of the generators in `U₈(ℤ[1/2, i])`. -/
noncomputable def semU (x : Gen) : U_ZHalfI 8 := ⟨sem x, sem_mem x⟩

end QCert.CliffordCS3
