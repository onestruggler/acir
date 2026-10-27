/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hadamard-Π, Theorem 4.13: soundness of Figure 6

Every relation of Figure 6 holds for the matrices: at symbolic indices in
dimension `n` it is the image of the same relation at the indices
`0, 1, …` in dimension at most 6, decided exactly over `ℤ√2`
(`QCert.HadamardPi.Local`).  Every generator is its own inverse by
(a1)–(a3), so the theory is grouplike.
-/
import QCert.HadamardPi.Local

namespace QCert.HadamardPi

open Matrix

/-- `f : Fin m → Fin n` given as a vector of indices is injective when its
entries are distinct (from the hypotheses in context). -/
macro "vec_inj" : tactic =>
  `(tactic| (intro i j hij; fin_cases i <;> fin_cases j <;>
    first | rfl | (simp at hij; done) | (simp at hij; exfalso; omega)))

/-- Discharge a relation by an exact check in dimension `m`. -/
macro "check_rel " f:term:max L:term:max R:term:max : tactic =>
  `(tactic| exact wordMat_eq_of_check $f (by vec_inj) $L $R (by decide +kernel) rfl rfl)

/-- Every relation of Figure 6 holds for the matrices. -/
theorem fig6_wordMat {n : ℕ} {w w' : Word (Gen n)} (h : Fig6 w w') :
    wordMat invSqrt2 w = wordMat invSqrt2 w' := by
  cases h with
  | a1 a => check_rel ![a] [.Z 0, .Z 0] []
  | @a2 a b hab => check_rel ![a, b] [.X 0 1, .X 0 1] []
  | @a3 a b hab => check_rel ![a, b] [.H 0 1, .H 0 1] []
  | @b1 a b hab => check_rel ![a, b] [.Z 0, .Z 1] [.Z 1, .Z 0]
  | @b2 a b c hbc hab hac => check_rel ![a, b, c] [.Z 0, .X 1 2] [.X 1 2, .Z 0]
  | @b3 a b c d hab hcd hac had hbc hbd =>
    check_rel ![a, b, c, d] [.X 0 1, .X 2 3] [.X 2 3, .X 0 1]
  | @b4 a b c hbc hab hac => check_rel ![a, b, c] [.Z 0, .H 1 2] [.H 1 2, .Z 0]
  | @b5 a b c d hab hcd hac had hbc hbd =>
    check_rel ![a, b, c, d] [.X 0 1, .H 2 3] [.H 2 3, .X 0 1]
  | @b6 a b c d hab hcd hac had hbc hbd =>
    check_rel ![a, b, c, d] [.H 0 1, .H 2 3] [.H 2 3, .H 0 1]
  | @c1 a b hab => check_rel ![a, b] [.Z 0, .X 0 1] [.X 0 1, .Z 1]
  | @c2 a b c hab hbc => check_rel ![a, b, c] [.X 1 2, .X 0 1] [.X 0 1, .X 0 2]
  | @c3 a b c hab hbc => check_rel ![a, b, c] [.X 0 2, .X 1 2] [.X 1 2, .X 0 1]
  | @c4 a b c hab hbc => check_rel ![a, b, c] [.H 1 2, .X 0 1] [.X 0 1, .H 0 2]
  | @c5 a b c hab hbc => check_rel ![a, b, c] [.H 0 2, .X 1 2] [.X 1 2, .H 0 1]
  | @d1 a b hab => check_rel ![a, b] [.Z 0, .Z 1, .H 0 1] [.H 0 1, .Z 0, .Z 1]
  | @d2 a b hab => check_rel ![a, b] [.Z 1, .H 0 1] [.H 0 1, .X 0 1]
  | @d3 a b c d hab hcd hac hbd hbc =>
    check_rel ![a, b, c, d] (List.replicate 4 [.H 2 3, .H 0 2, .H 1 3]).flatten [.H 0 1, .H 2 3]
  | @d4 a b c d e f hac hbd hab hce hdf hef hbc hbe hcd hde =>
    check_rel ![a, b, c, d, e, f]
      (List.replicate 3 [.H 0 2, .H 1 3, .H 0 1, .H 0 2, .H 1 3, .X 2 4, .X 3 5]).flatten
      [.H 2 4, .H 3 5, .H 4 5, .H 2 4, .H 3 5, .X 2 4, .X 3 5]

/-- Soundness of the axioms in `Oₙ(ℤ[1/√2])`. -/
theorem fig6_sound {n : ℕ} ⦃w w' : Word (Gen n)⦄ (h : Fig6 w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' := by
  apply Subtype.ext; apply Subtype.ext
  rw [lift_sem_val, lift_sem_val]
  exact fig6_wordMat h

/-- Every generator is its own inverse, by (a1)–(a3). -/
theorem fig6_grouplike {n : ℕ} : Grouplike (Fig6 (n := n)) := by
  intro x
  refine ⟨FreeMonoid.of x, Derivable.of ?_⟩
  cases x with
  | Z a => exact Fig6.a1 a
  | X a b h => exact Fig6.a2 h
  | H a b h => exact Fig6.a3 h

end QCert.HadamardPi
