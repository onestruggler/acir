/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): semantics

The matrices `X`, `H`, `K` of Definition 2.4, the generators as level
matrices (Definition 2.5, `levelMat` of the framework, indices from `0`),
the group `Oₙ(ℤ[1/2])` of Definition 2.3 (`O_ZHalf n` of the framework),
and the group `Lₙ` of orthogonal scaled dyadic matrices `N/√2^k`, `N` an
integer matrix (Definition 5.1), with the generator `I_{n/2} ⊗ H`.
-/
import QCert.LiRossSelinger.Syntax
import QCert.Matrix.Level
import QCert.Matrix.Rings
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace QCert.LiRossSelinger

open Matrix
open scoped Kronecker

noncomputable section

/-! ## Matrices -/

/-- The `1 × 1` matrix `−1`, the type of `(−1)_[a]`. -/
def matNeg : Matrix (Fin 1) (Fin 1) ℝ := !![-1]

/-- `X` of Definition 2.4. -/
def matX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `H` of Definition 2.4. -/
def matH : Matrix (Fin 2) (Fin 2) ℝ := (Real.sqrt 2)⁻¹ • !![1, 1; 1, -1]

/-- `K = H ⊗ H` of Definition 2.4. -/
def matK : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

variable {n : ℕ}

/-- The matrix of a generator: `(−1)_[a]`, `X_[a,b]`, `K_[a,b,c,d]` are the
level matrices of type `−1`, `X`, `K` (Definition 2.5). -/
def genMat : Gen n → Matrix (Fin n) (Fin n) ℝ
  | .neg a => levelMat ![a] matNeg
  | .x a b _ => levelMat ![a, b] matX
  | .k a b c d _ _ _ => levelMat ![a, b, c, d] matK

/-- `I_{n/2} ⊗ H`, `n = m * 2`, index `2i + j` for block `i`, position `j`. -/
def matIH (m : ℕ) : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ :=
  ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ matH).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-! ## The groups -/

/-- The orthogonal scaled dyadic matrices `N/√2^k`, `N` an integer matrix
(Definition 5.1), as a subgroup of the orthogonal group. -/
def scaledDyadic (n : ℕ) : Subgroup (unitaryGroup (Fin n) ℝ) where
  carrier := {U | ∃ (k : ℕ) (N : Matrix (Fin n) (Fin n) ℤ),
    (U : Matrix (Fin n) (Fin n) ℝ) = (Real.sqrt 2 ^ k)⁻¹ • N.map (Int.cast : ℤ → ℝ)}
  mul_mem' := by
    rintro U V ⟨k, N, hU⟩ ⟨l, M, hV⟩
    refine ⟨k + l, N * M, ?_⟩
    show (U : Matrix (Fin n) (Fin n) ℝ) * V = _
    have : N.map (Int.cast : ℤ → ℝ) * M.map Int.cast = (N * M).map Int.cast := by
      ext i j; simp [Matrix.mul_apply]
    rw [hU, hV, smul_mul_smul_comm, this, pow_add, mul_inv]
  one_mem' := ⟨0, 1, by simp [Matrix.map_one]⟩
  inv_mem' := by
    rintro U ⟨k, N, hU⟩
    refine ⟨k, Nᵀ, ?_⟩
    show star (U : Matrix (Fin n) (Fin n) ℝ) = _
    rw [hU, star_smul, star_trivial, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_map]

/-- `Lₙ`, the orthogonal scaled dyadic matrices of Definition 5.1. -/
abbrev L (n : ℕ) := scaledDyadic n

/-! ## Membership of the generators -/

theorem levelMat_mem_subring {R : Type*} [CommRing R] (S : Subring R) {m : ℕ}
    (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) (hM : ∀ i j, M i j ∈ S) (i j : Fin n) :
    levelMat f M i j ∈ S := by
  have hmul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) R) (B : Matrix (Fin l) (Fin p) R),
      (∀ i j, A i j ∈ S) → (∀ i j, B i j ∈ S) → ∀ i j, (A * B) i j ∈ S := by
    intro k l p A B hA hB i j
    rw [mul_apply]; exact Subring.sum_mem _ fun x _ => S.mul_mem (hA i x) (hB x j)
  have hE : ∀ i j, embedMat (R := R) f i j ∈ S := by
    intro i j; simp only [embedMat]; split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have h1 : ∀ {k : ℕ} (i j : Fin k), (1 : Matrix (Fin k) (Fin k) R) i j ∈ S := by
    intro k i j; rw [one_apply]; split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  simp only [levelMat, add_apply]
  refine S.add_mem (h1 i j) (hmul _ _ (hmul _ _ hE fun i j => ?_) (fun i j => hE j i) i j)
  rw [sub_apply]; exact S.sub_mem (hM i j) (h1 i j)

theorem half_mem_ZHalf : (2 : ℝ)⁻¹ ∈ ZHalf := Subring.subset_closure rfl

/-- Elements of `ℤ[1/2]` are `z / 2^k`. -/
theorem exists_of_mem_ZHalf {x : ℝ} (hx : x ∈ ZHalf) : ∃ (k : ℕ) (z : ℤ), x = z / 2 ^ k := by
  induction hx using Subring.closure_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact ⟨1, 1, by norm_num⟩
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, z, rfl⟩ := hx
    obtain ⟨l, w, rfl⟩ := hy
    refine ⟨k + l, z * 2 ^ l + w * 2 ^ k, ?_⟩
    rw [pow_add]; push_cast; field_simp
  | neg x _ hx =>
    obtain ⟨k, z, rfl⟩ := hx
    exact ⟨k, -z, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, z, rfl⟩ := hx
    obtain ⟨l, w, rfl⟩ := hy
    exact ⟨k + l, z * w, by rw [pow_add]; push_cast; field_simp⟩

/-- `Oₙ(ℤ[1/2]) ⊆ Lₙ`: a dyadic matrix has a common denominator `2^k = √2^{2k}`. -/
theorem O_ZHalf_le_L : O_ZHalf n ≤ L n := by
  intro U hU
  have h := fun i j => exists_of_mem_ZHalf ((mem_unitaryOver).1 hU i j)
  choose k z hz using h
  let K := Finset.univ.sup fun p : Fin n × Fin n => k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.le_sup (f := fun p : Fin n × Fin n => k p.1 p.2) (Finset.mem_univ (i, j))
  refine ⟨2 * K, fun i j => z i j * 2 ^ (K - k i j), ?_⟩
  ext i j
  rw [hz i j, smul_apply, map_apply, smul_eq_mul, pow_mul, Real.sq_sqrt (by norm_num)]
  have : (2 : ℝ) ^ K = 2 ^ (K - k i j) * 2 ^ k i j := by
    rw [← pow_add, Nat.sub_add_cancel (hk i j)]
  rw [this]; push_cast; field_simp

theorem matX_mem : matX ∈ unitaryGroup (Fin 2) ℝ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext i j; fin_cases i <;> fin_cases j <;> simp [matX, mul_apply, Fin.sum_univ_two]

theorem matNeg_mem : matNeg ∈ unitaryGroup (Fin 1) ℝ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext i j; fin_cases i; fin_cases j; simp [matNeg, mul_apply]

theorem matK_mem : matK ∈ unitaryGroup (Fin 4) ℝ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext i j; fin_cases i <;> fin_cases j <;> simp [matK, mul_apply, Fin.sum_univ_four] <;> norm_num

theorem matH_mem : matH ∈ unitaryGroup (Fin 2) ℝ := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matH, mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith

theorem injective_two {a b : Fin n} (h : a < b) : Function.Injective ![a, b] := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff] <;> omega

theorem injective_four {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Function.Injective ![a, b, c, d] := by
  simp only [Fin.lt_def] at hab hbc hcd
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff] <;> omega

theorem genMat_mem (g : Gen n) : genMat g ∈ unitaryGroup (Fin n) ℝ := by
  cases g with
  | neg a => exact levelMat_mem_unitaryGroup (fun i j _ => Subsingleton.elim i j) matNeg_mem
  | x a b h => exact levelMat_mem_unitaryGroup (injective_two h) matX_mem
  | k a b c d h₁ h₂ h₃ => exact levelMat_mem_unitaryGroup (injective_four h₁ h₂ h₃) matK_mem

theorem genMat_entries (g : Gen n) (i j : Fin n) : genMat g i j ∈ ZHalf := by
  have hhalf : ∀ s : ℤ, ((s : ℝ) * 2⁻¹) ∈ ZHalf := fun s =>
    ZHalf.mul_mem (intCast_mem ZHalf s) half_mem_ZHalf
  cases g with
  | neg a =>
    refine levelMat_mem_subring ZHalf _ _ (fun i j => ?_) i j
    fin_cases i; fin_cases j; simp [matNeg, ZHalf.neg_mem ZHalf.one_mem]
  | x a b h =>
    refine levelMat_mem_subring ZHalf _ _ (fun i j => ?_) i j
    fin_cases i <;> fin_cases j <;> simp [matX, ZHalf.zero_mem, ZHalf.one_mem]
  | k a b c d h₁ h₂ h₃ =>
    refine levelMat_mem_subring ZHalf _ _ (fun i j => ?_) i j
    fin_cases i <;> fin_cases j <;> simpa [matK] using (hhalf 1)

theorem matIH_mem (m : ℕ) : matIH m ∈ unitaryGroup (Fin (m * 2)) ℝ := by
  rw [matIH]
  apply (mem_unitaryGroup_iff).2
  rw [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
    conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_one, Matrix.one_mul,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 matH_mem, one_kronecker_one,
    submatrix_one_equiv]

theorem matIH_entries (m : ℕ) : ∃ (k : ℕ) (N : Matrix (Fin (m * 2)) (Fin (m * 2)) ℤ),
    matIH m = (Real.sqrt 2 ^ k)⁻¹ • N.map (Int.cast : ℤ → ℝ) := by
  refine ⟨1, ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ !![1, 1; 1, -1]).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm, ?_⟩
  ext i j
  simp only [matIH, submatrix_apply, smul_apply, map_apply, smul_eq_mul, pow_one]
  generalize finProdFinEquiv.symm i = x
  generalize finProdFinEquiv.symm j = y
  obtain ⟨a, p⟩ := x
  obtain ⟨b, q⟩ := y
  simp only [kronecker_apply, one_apply]
  split_ifs <;> fin_cases p <;> fin_cases q <;> simp [matH]

/-! ## The semantics -/

/-- The semantics of a generator in `Oₙ(ℤ[1/2])`. -/
def sem (n : ℕ) (g : Gen n) : O_ZHalf n :=
  ⟨⟨genMat g, genMat_mem g⟩, (mem_unitaryOver).2 (genMat_entries g)⟩

/-- The semantics of a generator of `𝓕ₙ` in `Lₙ`, `n = m * 2`. -/
def semL (m : ℕ) : GenL m → L (m * 2)
  | .base g => ⟨(sem (m * 2) g).1, O_ZHalf_le_L (sem (m * 2) g).2⟩
  | .ih => ⟨⟨matIH m, matIH_mem m⟩, matIH_entries m⟩

end

end QCert.LiRossSelinger
