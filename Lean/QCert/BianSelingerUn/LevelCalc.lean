/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Calculations with one- and two-level matrices

General facts about `levelMat` (from `QCert.Matrix.Level`) used by the
developments of Bian–Selinger (`QCert.BianSelingerUn`) and Greylyn
(`QCert.Greylyn`):

* `twoLevel a b U` and `oneLevel a z`, the two- and one-level matrices of
  the papers, for any indices (the papers only use `a < b`);
* `levelMat φ` is multiplicative for injective `φ`, and
  `levelMat φ (twoLevel a b U) = twoLevel (φ a) (φ b) U`: an identity
  between products of level matrices on the indices `0, …, m - 1` holds
  on any `m` distinct indices (`levelHom`), which reduces soundness of a
  relation at symbolic indices to one computation on `m × m` matrices;
* entries of level matrices, their action on vectors, and membership of
  their entries in a subring.
-/
import QCert.Matrix.Level
import QCert.Matrix.Rings

namespace QCert

open Matrix

section General

variable {R : Type*} [CommRing R] {n m k : ℕ}

theorem embedMat_mul_embedMat (φ : Fin m → Fin n) (g : Fin k → Fin m) :
    embedMat (R := R) φ * embedMat g = embedMat (φ ∘ g) := by
  ext i l
  simp only [mul_apply, embedMat, Function.comp_apply]
  rw [Finset.sum_eq_single (g l)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem levelMat_one (φ : Fin m → Fin n) : levelMat φ (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  simp [levelMat]

/-- A level matrix on injective indices is multiplicative. -/
theorem levelMat_mul {φ : Fin m → Fin n} (hφ : Function.Injective φ)
    (A B : Matrix (Fin m) (Fin m) R) : levelMat φ (A * B) = levelMat φ A * levelMat φ B := by
  have hE := embedMat_transpose_mul (R := R) hφ
  simp only [levelMat]
  set E := embedMat (R := R) φ
  have h1 : E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * ((A - 1) * (B - 1)) * Eᵀ := by
    calc E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * (A - 1) * (Eᵀ * E) * (B - 1) * Eᵀ := by
          simp only [Matrix.mul_assoc]
      _ = E * ((A - 1) * (B - 1)) * Eᵀ := by rw [hE, Matrix.mul_one, Matrix.mul_assoc E]
  have hAB : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, h1, hAB,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

/-- `levelMat φ` as a monoid homomorphism. -/
def levelHom {φ : Fin m → Fin n} (hφ : Function.Injective φ) :
    Matrix (Fin m) (Fin m) R →* Matrix (Fin n) (Fin n) R where
  toFun := levelMat φ
  map_one' := levelMat_one φ
  map_mul' := levelMat_mul hφ

@[simp] theorem levelHom_apply {φ : Fin m → Fin n} (hφ : Function.Injective φ)
    (A : Matrix (Fin m) (Fin m) R) : levelHom hφ A = levelMat φ A := rfl

/-- Level matrices compose. -/
theorem levelMat_levelMat (φ : Fin m → Fin n) (g : Fin k → Fin m) (M : Matrix (Fin k) (Fin k) R) :
    levelMat φ (levelMat g M) = levelMat (φ ∘ g) M := by
  simp only [levelMat, add_sub_cancel_left]
  rw [← embedMat_mul_embedMat, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem embedMat_map {S : Type*} [CommRing S] (h : R →+* S) (φ : Fin m → Fin n) :
    (embedMat (R := R) φ).map h = embedMat φ := by
  ext i j; simp only [embedMat, map_apply]; split_ifs <;> simp

theorem levelMat_map {S : Type*} [CommRing S] (h : R →+* S) (φ : Fin m → Fin n)
    (M : Matrix (Fin m) (Fin m) R) : (levelMat φ M).map h = levelMat φ (M.map h) := by
  simp only [levelMat]
  rw [Matrix.map_add _ (map_add h), Matrix.map_one _ h.map_zero h.map_one, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub h), Matrix.map_one _ h.map_zero h.map_one,
    Matrix.transpose_map, embedMat_map]

/-- The two-level matrix `U_[a,b]`: `U` on the basis vectors `a, b`. -/
def twoLevel (a b : Fin n) (U : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin n) (Fin n) R :=
  levelMat ![a, b] U

/-- The one-level matrix `z_[a]`: `z` at position `(a, a)`. -/
def oneLevel (a : Fin n) (z : R) : Matrix (Fin n) (Fin n) R :=
  levelMat ![a] !![z]

theorem levelMat_twoLevel (φ : Fin m → Fin n) (a b : Fin m) (U : Matrix (Fin 2) (Fin 2) R) :
    levelMat φ (twoLevel a b U) = twoLevel (φ a) (φ b) U := by
  rw [twoLevel, levelMat_levelMat, twoLevel]
  congr 1
  funext x; fin_cases x <;> rfl

theorem levelMat_oneLevel (φ : Fin m → Fin n) (a : Fin m) (z : R) :
    levelMat φ (oneLevel a z) = oneLevel (φ a) z := by
  rw [oneLevel, levelMat_levelMat, oneLevel]
  congr 1
  funext x; fin_cases x; rfl

theorem twoLevel_map {S : Type*} [CommRing S] (h : R →+* S) (a b : Fin n)
    (U : Matrix (Fin 2) (Fin 2) R) : (twoLevel a b U).map h = twoLevel a b (U.map h) :=
  levelMat_map h _ U

theorem oneLevel_map {S : Type*} [CommRing S] (h : R →+* S) (a : Fin n) (z : R) :
    (oneLevel a z).map h = oneLevel a (h z) := by
  rw [oneLevel, levelMat_map, oneLevel]
  congr 1
  ext i j; fin_cases i; fin_cases j; rfl

theorem injective_pair {a b : Fin n} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

theorem injective_single (a : Fin n) : Function.Injective ![a] := by
  intro x y _; exact Subsingleton.elim x y

/-- The entries of a two-level matrix. -/
theorem twoLevel_apply {a b : Fin n} (hab : a ≠ b) (U : Matrix (Fin 2) (Fin 2) R) (i j : Fin n) :
    twoLevel a b U i j =
      if i = a then (if j = a then U 0 0 else if j = b then U 0 1 else 0)
      else if i = b then (if j = a then U 1 0 else if j = b then U 1 1 else 0)
      else (1 : Matrix (Fin n) (Fin n) R) i j := by
  have hinj := injective_pair hab
  have e0 : ![a, b] 0 = a := rfl
  have e1 : ![a, b] 1 = b := rfl
  unfold twoLevel
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = i
    · subst hj; simpa using levelMat_apply_apply hinj U 0 0
    by_cases hj' : j = b
    · subst hj'; simpa [hj] using levelMat_apply_apply hinj U 0 1
    rw [levelMat_apply_of_right U i (fun l => by fin_cases l <;> simp <;> omega)]
    simp [hj, hj', Ne.symm hj]
  by_cases hi' : i = b
  · subst hi'
    by_cases hj : j = a
    · subst hj; simpa [hi] using levelMat_apply_apply hinj U 1 0
    by_cases hj' : j = i
    · subst hj'; simpa [hi] using levelMat_apply_apply hinj U 1 1
    rw [levelMat_apply_of_right U i (fun l => by fin_cases l <;> simp <;> omega)]
    simp [hi, hj, hj', Ne.symm hj']
  rw [levelMat_apply_of_left U (fun l => by fin_cases l <;> simp <;> omega)]
  simp [hi, hi']

/-- The entries of a one-level matrix. -/
theorem oneLevel_apply (a : Fin n) (z : R) (i j : Fin n) :
    oneLevel a z i j = if i = a ∧ j = a then z else (1 : Matrix (Fin n) (Fin n) R) i j := by
  unfold oneLevel
  by_cases hi : i = a
  · subst hi
    by_cases hj : j = i
    · subst hj; simpa using levelMat_apply_apply (injective_single j) !![z] 0 0
    rw [levelMat_apply_of_right _ _ (fun l => by fin_cases l; simp; omega)]
    simp [hj]
  rw [levelMat_apply_of_left _ (fun l => by fin_cases l; simp; omega)]
  simp [hi]

/-- A two-level matrix acts on the entries `a, b` of a vector. -/
theorem twoLevel_mulVec {a b : Fin n} (hab : a ≠ b) (U : Matrix (Fin 2) (Fin 2) R)
    (v : Fin n → R) :
    twoLevel a b U *ᵥ v = Function.update (Function.update v a (U 0 0 * v a + U 0 1 * v b)) b
      (U 1 0 * v a + U 1 1 * v b) := by
  funext i
  simp only [mulVec, dotProduct, twoLevel_apply hab]
  by_cases hi : i = b
  · subst hi
    rw [Function.update_self, Fintype.sum_eq_add a i hab]
    · simp [Ne.symm hab]
    · intro c ⟨hca, hci⟩; simp [Ne.symm hab, hca, hci]
  by_cases hi' : i = a
  · subst hi'
    rw [Function.update_of_ne hi, Function.update_self, Fintype.sum_eq_add i b hab]
    · simp [Ne.symm hab]
    · intro c ⟨hca, hcb⟩; simp [hca, hcb]
  rw [Function.update_of_ne hi, Function.update_of_ne hi']
  simp [hi, hi', one_apply]

/-- A one-level matrix scales one entry of a vector. -/
theorem oneLevel_mulVec (a : Fin n) (z : R) (v : Fin n → R) :
    oneLevel a z *ᵥ v = Function.update v a (z * v a) := by
  funext i
  simp only [mulVec, dotProduct, oneLevel_apply]
  by_cases hi : i = a
  · subst hi
    rw [Function.update_self, Finset.sum_eq_single i]
    · simp
    · intro c _ hc; simp [hc, Ne.symm hc]
    · simp
  rw [Function.update_of_ne hi]
  simp [hi, one_apply]

end General

section Subring

variable {n m : ℕ} {K : Type*} [CommRing K]

/-- A level matrix has its entries in any subring holding those of `M`. -/
theorem levelMat_mem {S : Subring K} {φ : Fin m → Fin n} (hφ : Function.Injective φ)
    {M : Matrix (Fin m) (Fin m) K} (hM : ∀ k l, M k l ∈ S) (i j : Fin n) :
    levelMat φ M i j ∈ S := by
  by_cases hi : ∃ k, φ k = i
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, φ l = j
    · obtain ⟨l, rfl⟩ := hj
      rw [levelMat_apply_apply hφ]; exact hM k l
    · simp only [not_exists] at hj
      rw [levelMat_apply_of_right M _ hj, one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
  · simp only [not_exists] at hi
    rw [levelMat_apply_of_left M hi, one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem

end Subring

end QCert
