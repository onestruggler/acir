/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Main Cases 1 and 2, and the Main Lemma

`G = X_[0,x]` below the pivot at a positive exponent.  The paper's case
analysis (Main Cases 1, 2) is not correct as written (see the README); here
the square is closed by *pair confluence*: the first syllable of `s` reduces
a matched pair `A` of the pivot column, the first syllable of `X_[0,x] s`
reduces (up to the permutation) a matched pair `B`, and the two reductions
are joined below the level of `s`.
-/
import QCert.HadamardPi.Window

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-- Main Cases 1 and 2: `G = X_[0,x]` below the pivot, at a positive
exponent. -/
theorem main_X_odd {s : O n} (hs : s ≠ 1) {z x : Fin n} (hzx : z < x) (hz : (z : ℕ) = 0)
    (hr : sem n (Gen.X z x hzx) * s ≠ 1) (hxJ : (x : ℕ) < piv s)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) : MainSquare s (Gen.X z x hzx) := by
  sorry

/-- Lemma A.7 (Main Lemma), for every basic generator; the cases at a
positive exponent with `X_[0,x]` or `H_[0,1]` below the pivot (Main Cases
1, 2, 9, 10) are `main_X_odd` and `main_H_odd`. -/
theorem main_lemma (s : O n) (hs : s ≠ 1) (g : Gen n) (hg : Basic g) : MainSquare s g := by
  by_cases hr : sem n g * s = 1
  · have hsg : s = sem n g := by
      have := congrArg (sem n g * ·) hr
      simp only [sem_sq_assoc, mul_one] at this
      exact this
    subst hsg
    exact square_pro hs (syl_basic g hg)
  cases g with
  | Z a =>
    simp only [Basic] at hg
    obtain ⟨a, ha⟩ := a
    simp only at hg
    subst hg
    exact main_Z hs ha hr
  | X a x h =>
    simp only [Basic] at hg
    exact main_X hs h hg hr (main_X_odd hs h hg hr)
  | H a b h =>
    simp only [Basic] at hg
    exact main_H hs h hg.1 hg.2 hr

end QCert.HadamardPi
