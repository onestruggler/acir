/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): generators acting on rows

Multiplying a matrix on the left by `(−1)_[a]` negates row `a`, by
`X_[a,b]` exchanges rows `a` and `b`, and by `K_[a,b,c,d]` replaces rows
`a, b, c, d` by their combinations `(r_a ± r_b ± r_c ± r_d)/2`; all other
rows are unchanged.
-/
import QCert.LiRossSelinger.Semantics

namespace QCert.LiRossSelinger

open Matrix

variable {n m : ℕ}

theorem levelMat_mul_of_not (f : Fin m → Fin n) (A : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hi : ∀ p, f p ≠ i) (j : Fin n) :
    (levelMat f A * M) i j = M i j := by
  rw [mul_apply]
  simp only [levelMat_apply_of_left A hi, one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem levelMat_mul_at {f : Fin m → Fin n} (hf : Function.Injective f)
    (A : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin m) (j : Fin n) :
    (levelMat f A * M) (f p) j = ∑ q, A p q * M (f q) j := by
  rw [mul_apply]
  have hsplit : ∑ l, levelMat f A (f p) l * M l j =
      ∑ l ∈ Finset.univ.image f, levelMat f A (f p) l * M l j := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro l _ hl
    have : ∀ q, f q ≠ l := fun q h => hl (Finset.mem_image.2 ⟨q, Finset.mem_univ _, h⟩)
    rw [levelMat_apply_of_right A _ this, one_apply, if_neg (fun h => this p h), zero_mul]
  rw [hsplit, Finset.sum_image (fun x _ y _ h => hf h)]
  simp only [levelMat_apply_apply hf]

/-- A level matrix leaves a column `e_i` with `i` outside its indices alone. -/
theorem levelMat_mul_unit {f : Fin m → Fin n} (A : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hi : ∀ p, f p ≠ i)
    (hM : ∀ r, M r i = if r = i then 1 else 0) (r : Fin n) :
    (levelMat f A * M) r i = if r = i then 1 else 0 := by
  rw [mul_apply]
  simp only [hM, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [levelMat_apply_of_right A _ hi, one_apply]

theorem genMat_neg_mul (a : Fin n) (M : Matrix (Fin n) (Fin n) ℝ) (r j : Fin n) :
    (genMat (Gen.neg a) * M) r j = if r = a then -M r j else M r j := by
  by_cases hr : r = a
  · subst hr
    rw [if_pos rfl]
    have := levelMat_mul_at (f := ![r]) (fun i j _ => Subsingleton.elim i j) matNeg M 0 j
    simpa [genMat, matNeg] using this
  · rw [if_neg hr]
    exact levelMat_mul_of_not _ _ M (fun p h => hr (by fin_cases p; exact h.symm)) j

theorem genMat_x_mul {a b : Fin n} (hab : a < b) (M : Matrix (Fin n) (Fin n) ℝ) (r j : Fin n) :
    (genMat (Gen.x a b hab) * M) r j =
      if r = a then M b j else if r = b then M a j else M r j := by
  have hf := injective_two hab
  by_cases ha : r = a
  · subst ha
    rw [if_pos rfl]
    have := levelMat_mul_at hf matX M 0 j
    simpa [genMat, matX, Fin.sum_univ_two] using this
  · by_cases hb : r = b
    · subst hb
      rw [if_neg ha, if_pos rfl]
      have := levelMat_mul_at hf matX M 1 j
      simpa [genMat, matX, Fin.sum_univ_two] using this
    · rw [if_neg ha, if_neg hb]
      exact levelMat_mul_of_not _ _ M (fun p h => by
        fin_cases p
        · exact ha h.symm
        · exact hb h.symm) j

theorem genMat_k_mul {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (M : Matrix (Fin n) (Fin n) ℝ) (r j : Fin n) :
    (genMat (Gen.k a b c d hab hbc hcd) * M) r j =
      if r = a then (M a j + M b j + M c j + M d j) / 2
      else if r = b then (M a j - M b j + M c j - M d j) / 2
      else if r = c then (M a j + M b j - M c j - M d j) / 2
      else if r = d then (M a j - M b j - M c j + M d j) / 2
      else M r j := by
  have hf := injective_four hab hbc hcd
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simp only [ne_eq, Fin.ext_iff]; simp only [Fin.lt_def] at hab hbc hcd; omega
  have at4 : ∀ p : Fin 4, (genMat (Gen.k a b c d hab hbc hcd) * M) (![a, b, c, d] p) j =
      ∑ q, matK p q * M (![a, b, c, d] q) j := fun p => levelMat_mul_at hf matK M p j
  by_cases ha : r = a
  · subst ha; rw [if_pos rfl]
    have := at4 0
    simp [matK, Fin.sum_univ_four] at this; rw [this]; ring
  by_cases hb : r = b
  · subst hb; rw [if_neg ha, if_pos rfl]
    have := at4 1
    simp [matK, Fin.sum_univ_four] at this; rw [this]; ring
  by_cases hc : r = c
  · subst hc; rw [if_neg ha, if_neg hb, if_pos rfl]
    have := at4 2
    simp [matK, Fin.sum_univ_four] at this; rw [this]; ring
  by_cases hd : r = d
  · subst hd; rw [if_neg ha, if_neg hb, if_neg hc, if_pos rfl]
    have := at4 3
    simp [matK, Fin.sum_univ_four] at this; rw [this]; ring
  rw [if_neg ha, if_neg hb, if_neg hc, if_neg hd]
  exact levelMat_mul_of_not _ _ M (fun p h => by
    fin_cases p
    · exact ha h.symm
    · exact hb h.symm
    · exact hc h.symm
    · exact hd h.symm) j

end QCert.LiRossSelinger
