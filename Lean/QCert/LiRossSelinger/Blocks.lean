/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Conjugation by `I ⊗ H`

The index `t` of `Fin (m * 2)` is the pair (block `t / 2`, position
`t % 2`) through `finProdFinEquiv`.  A level matrix along a block-aligned
map `blockMap β` (the blocks `β 0, …, β (k-1)` of `m`, in order) is
conjugated by `I_m ⊗ H` as its local matrix is by `I_k ⊗ H`
(`ih_conj_levelMat`).  So Table 2's relations reduce to identities of at
most `4 × 4` matrices.
-/
import QCert.LiRossSelinger.Semantics
import QCert.LiRossSelinger.LevelLemmas

namespace QCert.LiRossSelinger

open Matrix
open scoped Kronecker

variable {m k : ℕ}

/-- Block and position of an index. -/
abbrev bp (i : Fin (m * 2)) : Fin m × Fin 2 := finProdFinEquiv.symm i

theorem matIH_apply (i j : Fin (m * 2)) :
    matIH m i j = if (bp i).1 = (bp j).1 then matH (bp i).2 (bp j).2 else 0 := by
  rw [matIH, submatrix_apply, kroneckerMap_apply, one_apply]
  by_cases h : (bp i).1 = (bp j).1 <;> simp only [h, if_true, if_false, one_mul, zero_mul]

theorem matIH_mul_apply (X : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) (i j : Fin (m * 2)) :
    (matIH m * X) i j = ∑ p : Fin 2, matH (bp i).2 p * X (finProdFinEquiv ((bp i).1, p)) j := by
  rw [mul_apply, ← (finProdFinEquiv (m := m) (n := 2)).sum_comp, Fintype.sum_prod_type]
  simp only [matIH_apply, Equiv.symm_apply_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (bp i).1
    (fun b _ hb => by simp only [if_neg (Ne.symm hb), Finset.sum_const_zero]) (by simp)]
  simp only [if_true]

theorem mul_matIH_apply (X : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) (i j : Fin (m * 2)) :
    (X * matIH m) i j = ∑ q : Fin 2, X i (finProdFinEquiv ((bp j).1, q)) * matH q (bp j).2 := by
  rw [mul_apply, ← (finProdFinEquiv (m := m) (n := 2)).sum_comp, Fintype.sum_prod_type]
  simp only [matIH_apply, Equiv.symm_apply_apply, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (bp j).1
    (fun b _ hb => by simp only [if_neg hb, Finset.sum_const_zero]) (by simp)]
  simp only [if_true]

theorem matH_mul_matH : matH * matH = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matH, mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith

theorem matH_sum (a b : Fin 2) : ∑ p : Fin 2, matH a p * matH p b = if a = b then 1 else 0 := by
  have := congrFun (congrFun matH_mul_matH a) b
  rw [mul_apply, one_apply] at this; exact this

/-- The block-aligned index map of the blocks `β 0, …, β (k-1)`. -/
def blockMap (β : Fin k → Fin m) (t : Fin (k * 2)) : Fin (m * 2) :=
  finProdFinEquiv (β (bp t).1, (bp t).2)

theorem blockMap_injective {β : Fin k → Fin m} (hβ : Function.Injective β) :
    Function.Injective (blockMap β) := by
  intro s t h
  have := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at this
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (hβ this.1) this.2

theorem blockMap_pair (β : Fin k → Fin m) (b : Fin k) (p : Fin 2) :
    blockMap β (finProdFinEquiv (b, p)) = finProdFinEquiv (β b, p) := by
  simp [blockMap]

theorem conj_formula (X : Matrix (Fin (m * 2)) (Fin (m * 2)) ℝ) (i j : Fin (m * 2)) :
    (matIH m * X * matIH m) i j = ∑ p : Fin 2, ∑ q : Fin 2, matH (bp i).2 p *
      X (finProdFinEquiv ((bp i).1, p)) (finProdFinEquiv ((bp j).1, q)) * matH q (bp j).2 := by
  rw [mul_matIH_apply]
  simp only [matIH_mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Conjugating a block-aligned level matrix by `I ⊗ H`. -/
theorem ih_conj_levelMat {β : Fin k → Fin m} (hβ : Function.Injective β)
    (M : Matrix (Fin (k * 2)) (Fin (k * 2)) ℝ) :
    matIH m * levelMat (blockMap β) M * matIH m = levelMat (blockMap β) (matIH k * M * matIH k) := by
  have hf := blockMap_injective hβ
  ext i j
  rw [conj_formula]
  by_cases hi : ∃ b, β b = (bp i).1
  · obtain ⟨b, hb⟩ := hi
    have ei : i = blockMap β (finProdFinEquiv (b, (bp i).2)) := by
      rw [blockMap_pair, hb]; exact (finProdFinEquiv.apply_symm_apply i).symm
    by_cases hj : ∃ b', β b' = (bp j).1
    · obtain ⟨b', hb'⟩ := hj
      have ej : j = blockMap β (finProdFinEquiv (b', (bp j).2)) := by
        rw [blockMap_pair, hb']; exact (finProdFinEquiv.apply_symm_apply j).symm
      conv_rhs => rw [ei, ej, levelMat_apply_apply hf, conj_formula]
      simp only [Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← hb, ← hb', ← blockMap_pair, ← blockMap_pair, levelMat_apply_apply hf]
    · -- `j` outside the blocks: only the diagonal survives, and `i ≠ j`
      have hj' : ∀ q, ∀ l, blockMap β l ≠ finProdFinEquiv ((bp j).1, q) := by
        intro q l hl
        have := congrArg (fun t => (finProdFinEquiv.symm t).1) hl
        simp only [blockMap, Equiv.symm_apply_apply] at this
        exact hj ⟨_, this⟩
      have hj'' : ∀ l, blockMap β l ≠ j := by
        intro l hl; apply hj' (bp j).2 l; rw [hl]; exact (finProdFinEquiv.apply_symm_apply j).symm
      rw [levelMat_apply_of_right _ _ hj'']
      simp only [levelMat_apply_of_right _ _ (hj' _), one_apply]
      have hne : i ≠ j := by
        intro h; apply hj ⟨b, by rw [hb, h]⟩
      rw [if_neg hne]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg]; · simp
      intro h
      have := congrArg (fun t => (finProdFinEquiv.symm t).1) h
      simp only [Equiv.symm_apply_apply] at this
      exact hj ⟨b, by rw [hb, this]⟩
  · have hi' : ∀ p, ∀ l, blockMap β l ≠ finProdFinEquiv ((bp i).1, p) := by
      intro p l hl
      have := congrArg (fun t => (finProdFinEquiv.symm t).1) hl
      simp only [blockMap, Equiv.symm_apply_apply] at this
      exact hi ⟨_, this⟩
    have hi'' : ∀ l, blockMap β l ≠ i := by
      intro l hl; apply hi' (bp i).2 l; rw [hl]; exact (finProdFinEquiv.apply_symm_apply i).symm
    rw [levelMat_apply_of_left _ hi'']
    simp only [levelMat_apply_of_left _ (hi' _), one_apply]
    -- `∑ p q, H(i,p) [ (bi,p) = (bj,q) ] H(q,j) = δ`
    have key : ∀ p q : Fin 2, (finProdFinEquiv ((bp i).1, p) = finProdFinEquiv ((bp j).1, q)) ↔
        ((bp i).1 = (bp j).1 ∧ p = q) := by
      intro p q; rw [finProdFinEquiv.injective.eq_iff, Prod.mk.injEq]
    simp only [key]
    by_cases hb : (bp i).1 = (bp j).1
    · simp only [hb, true_and, mul_ite, mul_zero, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
      rw [matH_sum]
      congr 1
      apply propext
      constructor
      · intro h; apply finProdFinEquiv.symm.injective; exact Prod.ext hb h
      · intro h; rw [h]
    · simp only [hb, false_and, if_false, mul_zero, zero_mul, Finset.sum_const_zero]
      rw [if_neg]
      intro h; exact hb (by rw [h])

end QCert.LiRossSelinger
