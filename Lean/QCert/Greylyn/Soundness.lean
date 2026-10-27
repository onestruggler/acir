/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: soundness of the equations of Table 3.1

Lemma 23 (Soundness): each equation of Table 3.1 holds in
`Uₙ(ℤ[1/√2, i])`.  An equation on `m ≤ 4` distinct indices is the image of
the same equation on the indices `0, …, m - 1` (`transferHom`), checked
there by computation over `ℚ(ω)`.  Also: every generator is invertible
modulo the equations (`grouplike`), by (1)–(3).
-/
import QCert.Greylyn.Semantics
import QCert.BianSelingerUn.Transfer

namespace QCert.Greylyn

open Matrix

/-- `X` over `ℚ(ω)`. -/
def qX : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- `H` over `ℚ(ω)`. -/
def qH : Matrix (Fin 2) (Fin 2) QOmega :=
  !![QOmega.invSqrt2, QOmega.invSqrt2; QOmega.invSqrt2, -QOmega.invSqrt2]

/-- `ω ∈ ℚ(ω)`. -/
def qω : QOmega := Quartic.X

@[simp] theorem qX_map : qX.map QOmega.toC = Xmat := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [qX, Xmat, -Quartic.zero_def, -Quartic.one_def]

@[simp] theorem qH_map : qH.map QOmega.toC = Hmat := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [qH, Hmat, QOmega.toC_invSqrt2, -Quartic.neg_def]

@[simp] theorem toC_qω : QOmega.toC qω = QCert.ω := QOmega.toC_X

variable {n : ℕ}

/-- The matrix of a word: the product of the matrices of its letters. -/
noncomputable def matOf : Word (Gen n) →* Matrix (Fin n) (Fin n) ℂ := FreeMonoid.lift mat

@[simp] theorem matOf_of (x : Gen n) : matOf (FreeMonoid.of x) = mat x :=
  FreeMonoid.lift_eval_of _ _

theorem coe_lift_sem (w : Word (Gen n)) :
    (((FreeMonoid.lift (sem n) w : U_ZInvSqrt2I n) : unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = matOf w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => simp [ih]

/-- Two words with the same matrix have the same value. -/
theorem lift_sem_eq {w w' : Word (Gen n)} (h : matOf w = matOf w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift_sem, coe_lift_sem, h]

/-- Lemma 23: every equation of Table 3.1 holds for the matrices. -/
theorem matOf_sound {w w' : Word (Gen n)} (h : Rel n w w') : matOf w = matOf w' := by
  cases h with
  | r1 j =>
    have key : oneLevel (0 : Fin 1) qω ^ 8 = 1 := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_single j)) key
  | r2 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qH ^ 2 = 1 := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r3 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qX ^ 2 = 1 := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r4 j k hjk =>
    have key : oneLevel (0 : Fin 2) qω * oneLevel 1 qω = oneLevel 1 qω * oneLevel 0 qω := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk)) key
  | r5 j k l hjk hlj hlk =>
    have key : oneLevel (2 : Fin 3) qω * twoLevel 0 1 qH = twoLevel 0 1 qH * oneLevel 2 qω := by
      decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (Ne.symm hlj) (Ne.symm hlk))) key
  | r6 j k l hjk hlj hlk =>
    have key : oneLevel (2 : Fin 3) qω * twoLevel 0 1 qX = twoLevel 0 1 qX * oneLevel 2 qω := by
      decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (Ne.symm hlj) (Ne.symm hlk))) key
  | r7 j k l t hjk hlt hlj hlk htj htk =>
    have key : twoLevel (0 : Fin 4) 1 qH * twoLevel 2 3 qH = twoLevel 2 3 qH * twoLevel 0 1 qH := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_four hjk.ne (Ne.symm hlj)
      (Ne.symm htj) (Ne.symm hlk) (Ne.symm htk) hlt.ne)) key
  | r8 j k l t hjk hlt hlj hlk htj htk =>
    have key : twoLevel (0 : Fin 4) 1 qH * twoLevel 2 3 qX = twoLevel 2 3 qX * twoLevel 0 1 qH := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_four hjk.ne (Ne.symm hlj)
      (Ne.symm htj) (Ne.symm hlk) (Ne.symm htk) hlt.ne)) key
  | r9 j k l t hjk hlt hlj hlk htj htk =>
    have key : twoLevel (0 : Fin 4) 1 qX * twoLevel 2 3 qX = twoLevel 2 3 qX * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_four hjk.ne (Ne.symm hlj)
      (Ne.symm htj) (Ne.symm hlk) (Ne.symm htk) hlt.ne)) key
  | r10 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qX * oneLevel 1 qω = oneLevel 0 qω * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r11 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qX * oneLevel 0 qω = oneLevel 1 qω * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r12 j k l hjk hkl =>
    have key : twoLevel (0 : Fin 3) 1 qX * twoLevel 0 2 qX = twoLevel 1 2 qX * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r13 j k l hlj hjk =>
    have key : twoLevel (0 : Fin 3) 1 qX * twoLevel 2 0 qX = twoLevel 2 1 qX * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using congrArg (transferHom
      (injective_three hjk.ne (Ne.symm hlj.ne) (Ne.symm (hlj.trans hjk).ne))) key
  | r14 j k l hjk hkl =>
    have key : twoLevel (0 : Fin 3) 1 qX * twoLevel 0 2 qH = twoLevel 1 2 qH * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r15 j k l hlj hjk =>
    have key : twoLevel (0 : Fin 3) 1 qX * twoLevel 2 0 qH = twoLevel 2 1 qH * twoLevel 0 1 qX := by
      decide +kernel
    simpa [mat] using congrArg (transferHom
      (injective_three hjk.ne (Ne.symm hlj.ne) (Ne.symm (hlj.trans hjk).ne))) key
  | r16 j k hjk =>
    have key : oneLevel (0 : Fin 2) qω * oneLevel 1 qω * twoLevel 0 1 qX =
        twoLevel 0 1 qX * oneLevel 0 qω * oneLevel 1 qω := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r17 j k hjk =>
    have key : oneLevel (0 : Fin 2) qω * oneLevel 1 qω * twoLevel 0 1 qH =
        twoLevel 0 1 qH * oneLevel 0 qω * oneLevel 1 qω := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r18 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qH * twoLevel 0 1 qX = oneLevel 1 qω ^ 4 * twoLevel 0 1 qH := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r19 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qH * oneLevel 0 qω ^ 2 * twoLevel 0 1 qH =
        oneLevel 0 qω ^ 6 * twoLevel 0 1 qH * oneLevel 0 qω ^ 3 * oneLevel 1 qω ^ 5 := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r20 j k l t hjk hkl hlt =>
    have key : twoLevel (0 : Fin 4) 1 qH * twoLevel 2 3 qH * twoLevel 0 2 qH * twoLevel 1 3 qH =
        twoLevel 0 2 qH * twoLevel 1 3 qH * twoLevel 0 1 qH * twoLevel 2 3 qH := by
      decide +kernel
    simpa [mat] using congrArg (transferHom (injective_four hjk.ne (hjk.trans hkl).ne
      ((hjk.trans hkl).trans hlt).ne hkl.ne (hkl.trans hlt).ne hlt.ne)) key

/-- Lemma 23: the equations of Table 3.1 are sound for `Uₙ(ℤ[1/√2, i])`. -/
theorem sound {w w' : Word (Gen n)} (h : Rel n w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' :=
  lift_sem_eq (matOf_sound h)

/-- Every generator has an inverse modulo (1)–(3): `ω⁻¹ = ω⁷`, `H⁻¹ = H`,
`X⁻¹ = X`. -/
theorem grouplike : Grouplike (Rel n) := by
  intro x
  cases x with
  | X j k h => exact ⟨X j k h, by simpa [pow_two] using Derivable.of (Rel.r3 j k h)⟩
  | H j k h => exact ⟨H j k h, by simpa [pow_two] using Derivable.of (Rel.r2 j k h)⟩
  | ω j => exact ⟨ω j ^ 7, by simpa [← pow_succ] using Derivable.of (Rel.r1 j)⟩

end QCert.Greylyn
