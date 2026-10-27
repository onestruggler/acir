/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of real-Clifford+CH circuits

Definition 2.3: the gates of (A) as real matrices, on basis states
`|x⟩`, `|x, y⟩` with `x` on the upper wire.  In the framework a `2 × 2` or
`4 × 4` matrix is read on its wires with wire `0` (the bottom wire) as the
least significant bit (`ofMat`), so the row index of a two-wire matrix is
`2 x + y` with `x` on wire `1` (the control of `CH`) and `y` on wire `0`.

* `H = (1/√2) [[1, 1], [1, -1]]`,
* `Z = diag (1, -1)`,
* `CZ = diag (1, 1, 1, -1)`,
* `CH = diag (I, H)`, i.e. `|0, y⟩ ↦ |0, y⟩` and
  `|1, y⟩ ↦ (|1, 0⟩ + (-1)^y |1, 1⟩)/√2`.

The same matrices over the computable field ℚ(√2) (`opsQ`) are mapped onto
these by `QSqrt2.toR` (`toOps_eq`), so that identities can be decided there.
-/
import QCert.RealCliffordCH.Syntax
import QCert.Circuit.Eval
import QCert.Exact.Roots

namespace QCert.RealCliffordCH

open Matrix

noncomputable section

/-- `1/√2`. -/
abbrev invSqrt2 : ℝ := (Real.sqrt 2)⁻¹

/-- The Hadamard matrix. -/
def matH : Matrix (Fin 2) (Fin 2) ℝ := !![invSqrt2, invSqrt2; invSqrt2, -invSqrt2]

/-- The Pauli `Z` matrix. -/
def matZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- The controlled-`Z` matrix. -/
def matCZ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- The controlled-Hadamard matrix, control on the upper wire. -/
def matCH : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, invSqrt2, invSqrt2; 0, 0, invSqrt2, -invSqrt2]

end

/-! ## The same matrices over ℚ(√2) -/

/-- `H` over ℚ(√2). -/
def qH : Matrix (Fin 2) (Fin 2) QSqrt2 :=
  !![QSqrt2.invSqrt2, QSqrt2.invSqrt2; QSqrt2.invSqrt2, -QSqrt2.invSqrt2]

/-- `Z` over ℚ(√2). -/
def qZ : Matrix (Fin 2) (Fin 2) QSqrt2 := !![1, 0; 0, -1]

/-- `CZ` over ℚ(√2). -/
def qCZ : Matrix (Fin 4) (Fin 4) QSqrt2 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- `CH` over ℚ(√2). -/
def qCH : Matrix (Fin 4) (Fin 4) QSqrt2 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, QSqrt2.invSqrt2, QSqrt2.invSqrt2;
    0, 0, QSqrt2.invSqrt2, -QSqrt2.invSqrt2]

/-- The gates as operators over ℚ(√2). -/
def opsQ : GateOps Gate QSqrt2 2 where
  scalar g := nomatch g
  gate1
    | .H => ofMat (k := 1) qH
    | .Z => ofMat (k := 1) qZ
  gate2
    | .CZ => ofMat (k := 2) qCZ
    | .CH => ofMat (k := 2) qCH
  gate3 g := nomatch g

theorem matH_eq : matH = qH.map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matH, qH, QSqrt2.toR_invSqrt2, -Quadratic.one_def, -Quadratic.zero_def, -Quadratic.neg_def]

theorem matZ_eq : matZ = qZ.map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ, qZ, -Quadratic.one_def, -Quadratic.zero_def, -Quadratic.neg_def]

theorem matCZ_eq : matCZ = qCZ.map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matCZ, qCZ, -Quadratic.one_def, -Quadratic.zero_def, -Quadratic.neg_def]

theorem matCH_eq : matCH = qCH.map QSqrt2.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matCH, qCH, QSqrt2.toR_invSqrt2, -Quadratic.one_def, -Quadratic.zero_def, -Quadratic.neg_def]

/-- A matrix over ℚ(√2) whose transpose is its inverse maps to an orthogonal
real matrix. -/
theorem map_mem_unitaryGroup {m : ℕ} (M : Matrix (Fin m) (Fin m) QSqrt2)
    (hM : M * Mᵀ = 1) : M.map QSqrt2.toR ∈ unitaryGroup (Fin m) ℝ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    ← transpose_map, ← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem matH_mem : matH ∈ unitaryGroup (Fin 2) ℝ := by
  rw [matH_eq]; exact map_mem_unitaryGroup _ (by decide +kernel)

theorem matZ_mem : matZ ∈ unitaryGroup (Fin 2) ℝ := by
  rw [matZ_eq]; exact map_mem_unitaryGroup _ (by decide +kernel)

theorem matCZ_mem : matCZ ∈ unitaryGroup (Fin 4) ℝ := by
  rw [matCZ_eq]; exact map_mem_unitaryGroup _ (by decide +kernel)

theorem matCH_mem : matCH ∈ unitaryGroup (Fin 4) ℝ := by
  rw [matCH_eq]; exact map_mem_unitaryGroup _ (by decide +kernel)

/-- Definition 2.3: the semantics of the gates, as orthogonal real matrices. -/
noncomputable def S : GateSem Gate ℝ 2 where
  scalar g := nomatch g
  gate1
    | .H => ⟨ofMat (k := 1) matH, ofMat_mem_unitaryGroup matH_mem⟩
    | .Z => ⟨ofMat (k := 1) matZ, ofMat_mem_unitaryGroup matZ_mem⟩
  gate2
    | .CZ => ⟨ofMat (k := 2) matCZ, ofMat_mem_unitaryGroup matCZ_mem⟩
    | .CH => ⟨ofMat (k := 2) matCH, ofMat_mem_unitaryGroup matCH_mem⟩
  gate3 g := nomatch g

theorem ofMat_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') {k : ℕ}
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R) :
    ofMat (d := 2) (M.map f) = (ofMat M).map f := rfl

/-- The real gates are the images of the ones over ℚ(√2). -/
theorem toOps_eq : S.toOps = opsQ.map QSqrt2.toR := by
  show GateOps.mk _ _ _ _ = GateOps.mk _ _ _ _
  congr 1
  · funext g; exact nomatch g
  · funext g; cases g
    · show ofMat (d := 2) (k := 1) matH = (ofMat (d := 2) (k := 1) qH).map _; rw [matH_eq]; rfl
    · show ofMat (d := 2) (k := 1) matZ = (ofMat (d := 2) (k := 1) qZ).map _; rw [matZ_eq]; rfl
  · funext g; cases g
    · show ofMat (d := 2) (k := 2) matCZ = (ofMat (d := 2) (k := 2) qCZ).map _; rw [matCZ_eq]; rfl
    · show ofMat (d := 2) (k := 2) matCH = (ofMat (d := 2) (k := 2) qCH).map _; rw [matCH_eq]; rfl
  · funext g; exact nomatch g

end QCert.RealCliffordCH
