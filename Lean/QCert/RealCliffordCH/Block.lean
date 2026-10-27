/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Operators that are block diagonal in their top wires

An operator on `m + k` wires is *block diagonal in the top `m` wires* when
it never changes them: on each value `h` of the top wires it acts by an
operator `F h` on the bottom `k` wires (`blk F`).  Operators on the bottom
wires (`onBottom`) and diagonal operators are of this form, and so are
their products, computed block by block (`blk_mul`).  This reduces a
statement about operators at every width to one about operators on `k`
wires, which can be decided.
-/
import QCert.Circuit.Semantics

namespace QCert.RealCliffordCH

open Matrix

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The operator acting by `F h` on the bottom `k` wires when the top `m`
wires are `h`. -/
def blk {m k : ℕ} (F : State d m → Op R d k) : Op R d (m + k) :=
  fun s t => if (split d m k s).2 = (split d m k t).2
    then F (split d m k s).2 (split d m k s).1 (split d m k t).1 else 0

theorem onBottom_eq_blk {m k : ℕ} (A : Op R d k) : onBottom (n := m) A = blk fun _ => A := by
  ext s t; rw [onBottom_apply]; rfl

theorem blk_mul {m k : ℕ} (F G : State d m → Op R d k) :
    blk F * blk G = blk fun h => F h * G h := by
  ext s t
  rw [mul_apply, ← (split d m k).symm.sum_comp, Fintype.sum_prod_type]
  simp only [blk, Equiv.apply_symm_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases hab : (split d m k s).2 = (split d m k t).2
  · rw [if_pos hab, mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single (split d m k s).2]
    · simp [hab]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun h _ => ?_
    by_cases h1 : (split d m k s).2 = h
    · subst h1; simp [hab]
    · simp [h1]

/-- A diagonal operator is block diagonal in any top wires. -/
theorem diagonal_eq_blk {m k : ℕ} (e : State d (m + k) → R) :
    diagonal e = blk fun h => diagonal fun l => e ((split d m k).symm (l, h)) := by
  ext s t
  simp only [blk, diagonal_apply]
  by_cases hst : s = t
  · subst hst; simp
  · have hne : split d m k s ≠ split d m k t := (split d m k).injective.ne hst
    rw [if_neg hst]
    split_ifs with h2 h1
    · exact (hne (Prod.ext h1 h2)).elim
    · rfl
    · rfl

/-- A diagonal operator moved up is diagonal. -/
theorem onTop_diagonal {n : ℕ} (k : ℕ) (e : State d n → R) :
    onTop k (diagonal e) = diagonal fun s => e (split d n k s).2 := by
  ext s t
  rw [onTop_apply, diagonal_apply, diagonal_apply]
  by_cases hst : s = t
  · subst hst; simp
  · have hne : split d n k s ≠ split d n k t := (split d n k).injective.ne hst
    rw [if_neg hst]
    split_ifs with h1 h2
    · exact (hne (Prod.ext h1 h2)).elim
    · rfl
    · rfl

/-- A diagonal operator on the bottom wires is diagonal. -/
theorem onBottom_diagonal {n k : ℕ} (e : State d k → R) :
    onBottom (n := n) (diagonal e) = diagonal fun s => e (split d n k s).1 := by
  ext s t
  rw [onBottom_apply, diagonal_apply, diagonal_apply]
  by_cases hst : s = t
  · subst hst; simp
  · have hne : split d n k s ≠ split d n k t := (split d n k).injective.ne hst
    rw [if_neg hst]
    split_ifs with h1 h2
    · exact (hne (Prod.ext h2 h1)).elim
    · rfl
    · rfl

end QCert.RealCliffordCH
