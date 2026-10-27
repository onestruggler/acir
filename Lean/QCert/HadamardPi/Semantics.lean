/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-Π, §4.2: the matrices of the generators

The generator `(-1)_[a]` is the one-level matrix `-1` at index `a`, and
`X_[a,b]`, `H_[a,b]` are the two-level matrices of
`X = [[0,1],[1,0]]` and `H = (1/√2)[[1,1],[1,-1]]` at indices `a, b`
(Definitions 4.4 and 4.5), `levelMat ![a, b] M` in the notation of
`QCert.Matrix.Level`.  The matrices are defined over any commutative ring
with an element `s` standing for `1/√2` (`genMat s`), so that identities
can be computed exactly elsewhere; the semantics `sem n` takes `s = 1/√2`
in `ℝ`, where every generator is an orthogonal matrix with entries in
`ℤ[1/√2]`: an element of `Oₙ(ℤ[1/√2])` (Definition 4.3, `O_ZInvSqrt2 n`).
A word denotes the product of its letters (Definition 4.12).
-/
import QCert.HadamardPi.Syntax
import QCert.Matrix.Level
import QCert.Matrix.Rings

namespace QCert.HadamardPi

open Matrix

section Matrices

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The `1 × 1` matrix `-1`. -/
def Zmat : Matrix (Fin 1) (Fin 1) R := !![-1]

/-- `X = [[0,1],[1,0]]`. -/
def Xmat : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- `H = s [[1,1],[1,-1]]`, with `s` standing for `1/√2`. -/
def Hmat (s : R) : Matrix (Fin 2) (Fin 2) R := !![s, s; s, -s]

/-- The matrix of a generator, with `s` standing for `1/√2`. -/
def genMat (s : R) : Gen n → Matrix (Fin n) (Fin n) R
  | .Z a => levelMat ![a] Zmat
  | .X a b _ => levelMat ![a, b] Xmat
  | .H a b _ => levelMat ![a, b] (Hmat s)

/-- The matrix of a word: the product of its letters. -/
def wordMat (s : R) : Word (Gen n) →* Matrix (Fin n) (Fin n) R := FreeMonoid.lift (genMat s)

end Matrices

/-- `1/√2`. -/
noncomputable abbrev invSqrt2 : ℝ := (Real.sqrt 2)⁻¹

theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 + invSqrt2 * invSqrt2 = 1 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  linarith

theorem invSqrt2_mem : invSqrt2 ∈ ZInvSqrt2 := Subring.subset_closure rfl

section Unitary

theorem Zmat_mem : (Zmat : Matrix (Fin 1) (Fin 1) ℝ) ∈ unitaryGroup (Fin 1) ℝ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i; fin_cases j; simp [Zmat, mul_apply, star_trivial]

theorem Xmat_mem : (Xmat : Matrix (Fin 2) (Fin 2) ℝ) ∈ unitaryGroup (Fin 2) ℝ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Xmat, mul_apply, Fin.sum_univ_two]

theorem Hmat_mem : Hmat invSqrt2 ∈ unitaryGroup (Fin 2) ℝ := by
  rw [mem_unitaryGroup_iff]
  have h := invSqrt2_mul_self
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Hmat, mul_apply, Fin.sum_univ_two, h]

theorem vecCons_injective₁ {n : ℕ} (a : Fin n) : Function.Injective ![a] := by
  intro i j _; exact Subsingleton.elim i j

theorem vecCons_injective₂ {n : ℕ} {a b : Fin n} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; exact absurd hij (by omega))

theorem genMat_mem_unitary {n : ℕ} (g : Gen n) :
    genMat invSqrt2 g ∈ unitaryGroup (Fin n) ℝ := by
  cases g with
  | Z a => exact levelMat_mem_unitaryGroup (vecCons_injective₁ a) Zmat_mem
  | X a b h => exact levelMat_mem_unitaryGroup (vecCons_injective₂ (ne_of_lt h)) Xmat_mem
  | H a b h => exact levelMat_mem_unitaryGroup (vecCons_injective₂ (ne_of_lt h)) Hmat_mem

/-- The entries of a level matrix are entries of `M`, `0` or `1`, combined
by ring operations. -/
theorem levelMat_apply_mem {m n : ℕ} {S : Subring ℝ} (f : Fin m → Fin n)
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : ∀ k l, M k l ∈ S) (i j : Fin n) :
    levelMat f M i j ∈ S := by
  have h01 : ∀ (p : Prop) [Decidable p], (if p then (1 : ℝ) else 0) ∈ S := fun p _ => by
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  simp only [levelMat, add_apply, mul_apply, embedMat, transpose_apply, sub_apply, one_apply]
  exact S.add_mem (h01 _) (S.sum_mem fun l _ => S.mul_mem
    (S.sum_mem fun k _ => S.mul_mem (h01 _) (S.sub_mem (hM k l) (h01 _))) (h01 _))

theorem genMat_mem_ZInvSqrt2 {n : ℕ} (g : Gen n) (i j : Fin n) :
    genMat invSqrt2 g i j ∈ ZInvSqrt2 := by
  cases g with
  | Z a =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k; fin_cases l; simp [Zmat, ZInvSqrt2.neg_mem, ZInvSqrt2.one_mem]
  | X a b h =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k <;> fin_cases l <;> simp [Xmat, ZInvSqrt2.one_mem, ZInvSqrt2.zero_mem]
  | H a b h =>
    refine levelMat_apply_mem _ (fun k l => ?_) i j
    fin_cases k <;> fin_cases l <;> simp [Hmat, invSqrt2_mem, ZInvSqrt2.neg_mem]

end Unitary

/-- The semantics of a generator: its matrix, an element of
`Oₙ(ℤ[1/√2])`. -/
noncomputable def sem (n : ℕ) (g : Gen n) : O_ZInvSqrt2 n :=
  ⟨⟨genMat invSqrt2 g, genMat_mem_unitary g⟩, genMat_mem_ZInvSqrt2 g⟩

/-- The value of a word, as a matrix, is the product of its letters. -/
theorem lift_sem_val {n : ℕ} (w : Word (Gen n)) :
    (((FreeMonoid.lift (sem n) w : O_ZInvSqrt2 n) : unitaryGroup (Fin n) ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = wordMat invSqrt2 w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih]
    rfl

end QCert.HadamardPi
