/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément (2019), Section 3.5: soundness of (1)–(22)

Every relation holds for the matrices: at symbolic indices it is the image
of the same relation at `0, 1, …` in dimension at most 6, decided exactly
over `ℤ√2` (`QCert.HadamardPi.Local`).  Every generator is its own inverse
by (1)–(3), so the theory is grouplike.
-/
import QCert.Clement2019.Semantics
import QCert.HadamardPi.Soundness

namespace QCert.Clement2019

open Matrix QCert.HadamardPi

/-- Discharge a relation by an exact check in dimension `m`. -/
macro "check_relC " f:term:max L:term:max R:term:max : tactic =>
  `(tactic| exact wordMat_eq_of_check $f (by vec_inj) $L $R (by decide +kernel) rfl rfl)

/-- Every relation (1)–(22) holds for the matrices. -/
theorem rel_wordMat {n : ℕ} {w w' : Word (Gen n)} (h : Rel w w') :
    wordMat invSqrt2 w = wordMat invSqrt2 w' := by
  cases h with
  | r1 j => check_relC ![j] [.Z 0, .Z 0] []
  | @r2 j k hjk => check_relC ![j, k] [.H 0 1, .H 0 1] []
  | @r3 j k hjk => check_relC ![j, k] [.X 0 1, .X 0 1] []
  | @r4 j k hjk => check_relC ![j, k] [.Z 0, .Z 1] [.Z 1, .Z 0]
  | @r5 j k l hjk hlj hlk => check_relC ![j, k, l] [.Z 2, .H 0 1] [.H 0 1, .Z 2]
  | @r6 j k l hjk hlj hlk => check_relC ![j, k, l] [.Z 2, .X 0 1] [.X 0 1, .Z 2]
  | @r7 j k l t hjk hlt hjl hjt hkl hkt =>
    check_relC ![j, k, l, t] [.H 0 1, .H 2 3] [.H 2 3, .H 0 1]
  | @r8 j k l t hjk hlt hjl hjt hkl hkt =>
    check_relC ![j, k, l, t] [.H 0 1, .X 2 3] [.X 2 3, .H 0 1]
  | @r9 j k l t hjk hlt hjl hjt hkl hkt =>
    check_relC ![j, k, l, t] [.X 0 1, .X 2 3] [.X 2 3, .X 0 1]
  | @r10 j k hjk => check_relC ![j, k] [.X 0 1, .Z 1] [.Z 0, .X 0 1]
  | @r11 j k hjk => check_relC ![j, k] [.X 0 1, .Z 0] [.Z 1, .X 0 1]
  | @r12 j k l hjk hjl hkl => check_relC ![j, k, l] [.X 0 1, .X 0 2] [.X 1 2, .X 0 1]
  | @r13 j k l hjk hjl hkl => check_relC ![j, k, l] [.X 0 1, .X 2 0] [.X 2 1, .X 0 1]
  | @r14 j k l hjk hjl hkl => check_relC ![j, k, l] [.X 0 1, .H 0 2] [.H 1 2, .X 0 1]
  | @r15 j k l hjk hjl hkl => check_relC ![j, k, l] [.X 0 1, .H 2 0] [.H 2 1, .X 0 1]
  | @r16 j k hjk => check_relC ![j, k] [.Z 0, .Z 1, .X 0 1] [.X 0 1, .Z 0, .Z 1]
  | @r17 j k hjk => check_relC ![j, k] [.Z 0, .Z 1, .H 0 1] [.H 0 1, .Z 0, .Z 1]
  | @r18 j k hjk => check_relC ![j, k] [.H 0 1, .X 0 1] [.Z 1, .H 0 1]
  | @r19 j k l t hjk hlt hjl hkt hjt =>
    by_cases hkl : k = l
    · subst hkl; rfl
    · check_relC ![j, k, l, t] [.H 0 1, .H 2 3, .H 0 2, .H 1 3] [.H 0 2, .H 1 3, .H 0 1, .H 2 3]
  | r20 hn =>
    check_relC ![idx 0, idx 1, idx 2, idx 3]
      [.H 0 1, .H 0 2, .H 1 3, .H 0 1, .Z 0, .Z 1, .H 0 2, .H 1 3]
      [.H 0 2, .H 1 3, .H 0 1, .Z 0, .Z 1, .H 0 2, .H 1 3, .H 0 1]
  | r21 hn =>
    check_relC ![idx 0, idx 1, idx 2, idx 3, idx 4, idx 5]
      [.H 0 1, .H 0 2, .H 1 3, .H 0 4, .H 1 5, .H 0 1, .Z 0, .Z 1, .H 0 4, .H 1 5, .H 0 2, .H 1 3]
      [.H 0 2, .H 1 3, .H 0 4, .H 1 5, .H 0 1, .Z 0, .Z 1, .H 0 4, .H 1 5, .H 0 2, .H 1 3, .H 0 1]
  | @r22 hn j k hjk => check_relC ![j, k] [.X 0 1, .H 0 1] [.H 1 0, .X 0 1]

/-- Soundness of the axioms in `Oₙ(ℤ[1/√2])` (Section 3.5). -/
theorem rel_sound {n : ℕ} ⦃w w' : Word (Gen n)⦄ (h : Rel w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' := by
  apply Subtype.ext; apply Subtype.ext
  rw [lift_sem_val, lift_sem_val]
  exact rel_wordMat h

/-- Every generator is its own inverse, by (1)–(3). -/
theorem rel_grouplike {n : ℕ} : Grouplike (Rel (n := n)) := by
  intro x
  refine ⟨FreeMonoid.of x, Derivable.of ?_⟩
  cases x with
  | Z j => exact Rel.r1 j
  | H j k h => exact Rel.r2 h
  | X j k h => exact Rel.r3 h

end QCert.Clement2019
