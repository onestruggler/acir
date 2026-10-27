/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: soundness of the relations of Figure 1

Remark 3.2: each relation of Figure 1 holds in `Uₙ(ℤ[1/2, i])`.  A relation
on `m ≤ 4` distinct indices is the image of the same relation on the
indices `0, …, m - 1` (`transferHom`), checked there by computation over
`ℚ(ω)`.  Also: every generator is invertible modulo the relations
(`grouplike`), by (1)–(3).
-/
import QCert.BianSelingerUn.Semantics
import QCert.BianSelingerUn.Transfer

namespace QCert.BianSelingerUn

open Matrix

/-- `X` over `ℚ(ω)`. -/
def qX : Matrix (Fin 2) (Fin 2) QOmega := !![0, 1; 1, 0]

/-- `1/(1+i) = (1 - ω²)/2 ∈ ℚ(ω)`. -/
def qc : QOmega := ⟨1 / 2, 0, -1 / 2, 0⟩

/-- `K` over `ℚ(ω)`. -/
def qK : Matrix (Fin 2) (Fin 2) QOmega := !![qc, qc; qc, -qc]

theorem toC_qc : QOmega.toC qc = (1 + Complex.I)⁻¹ := by
  rw [inv_one_add_I]
  simp only [QOmega.toC, Quartic.lift_apply, qc, ω_sq]
  push_cast; ring

@[simp] theorem qX_map : qX.map QOmega.toC = Xmat := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [qX, Xmat, -Quartic.zero_def, -Quartic.one_def]

@[simp] theorem qK_map : qK.map QOmega.toC = Kmat := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [qK, Kmat, toC_qc, -Quartic.neg_def]

variable {n : ℕ}

/-- The matrix of a word: the product of the matrices of its letters. -/
noncomputable def matOf : Word (Gen n) →* Matrix (Fin n) (Fin n) ℂ := FreeMonoid.lift mat

@[simp] theorem matOf_of (x : Gen n) : matOf (FreeMonoid.of x) = mat x :=
  FreeMonoid.lift_eval_of _ _

theorem coe_lift_sem (w : Word (Gen n)) :
    (((FreeMonoid.lift (sem n) w : U_ZHalfI n) : unitaryGroup (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) = matOf w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih => simp [ih]

/-- Two words with the same matrix have the same value. -/
theorem lift_sem_eq {w w' : Word (Gen n)} (h : matOf w = matOf w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift_sem, coe_lift_sem, h]

/-- Remark 3.2: every relation of Figure 1 holds for the matrices. -/
theorem matOf_sound {w w' : Word (Gen n)} (h : Rel n w w') : matOf w = matOf w' := by
  cases h with
  | r1 j =>
    have key : oneLevel (0 : Fin 1) QOmega.I ^ 4 = 1 := by decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_single j)) key
  | r2 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qX ^ 2 = 1 := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r3 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qK ^ 8 = 1 := by decide +kernel
    simpa [mat] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r4 j k hjk =>
    have key : oneLevel (0 : Fin 2) QOmega.I * oneLevel 1 QOmega.I =
        oneLevel 1 QOmega.I * oneLevel 0 QOmega.I := by decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk)) key
  | r5 j k l hkl hjk hjl =>
    have key : oneLevel (0 : Fin 3) QOmega.I * twoLevel 1 2 qX =
        twoLevel 1 2 qX * oneLevel 0 QOmega.I := by decide +kernel
    simpa [mat, QOmega.toC_I] using
      congrArg (transferHom (injective_three hjk hjl hkl.ne)) key
  | r6 j k l hkl hjk hjl =>
    have key : oneLevel (0 : Fin 3) QOmega.I * twoLevel 1 2 qK =
        twoLevel 1 2 qK * oneLevel 0 QOmega.I := by decide +kernel
    simpa [mat, QOmega.toC_I] using
      congrArg (transferHom (injective_three hjk hjl hkl.ne)) key
  | r7 j k l m hjk hlm hjl hjm hkl hkm =>
    have key : twoLevel (0 : Fin 4) 1 qX * twoLevel 2 3 qX =
        twoLevel 2 3 qX * twoLevel 0 1 qX := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_four hjk.ne hjl hjm hkl hkm hlm.ne)) key
  | r8 j k l m hjk hlm hjl hjm hkl hkm =>
    have key : twoLevel (0 : Fin 4) 1 qX * twoLevel 2 3 qK =
        twoLevel 2 3 qK * twoLevel 0 1 qX := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_four hjk.ne hjl hjm hkl hkm hlm.ne)) key
  | r9 j k l m hjk hlm hjl hjm hkl hkm =>
    have key : twoLevel (0 : Fin 4) 1 qK * twoLevel 2 3 qK =
        twoLevel 2 3 qK * twoLevel 0 1 qK := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_four hjk.ne hjl hjm hkl hkm hlm.ne)) key
  | r10 j k hjk =>
    have key : oneLevel (1 : Fin 2) QOmega.I * twoLevel 0 1 qX =
        twoLevel 0 1 qX * oneLevel 0 QOmega.I := by decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r11 j k l hjk hkl =>
    have key : twoLevel (1 : Fin 3) 2 qX * twoLevel 0 1 qX =
        twoLevel 0 1 qX * twoLevel 0 2 qX := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r12 j k l hjk hkl =>
    have key : twoLevel (0 : Fin 3) 2 qX * twoLevel 1 2 qX =
        twoLevel 1 2 qX * twoLevel 0 1 qX := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r13 j k l hjk hkl =>
    have key : twoLevel (1 : Fin 3) 2 qK * twoLevel 0 1 qX =
        twoLevel 0 1 qX * twoLevel 0 2 qK := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r14 j k l hjk hkl =>
    have key : twoLevel (0 : Fin 3) 2 qK * twoLevel 1 2 qX =
        twoLevel 1 2 qX * twoLevel 0 1 qK := by decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_three hjk.ne (hjk.trans hkl).ne hkl.ne)) key
  | r15 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qK * oneLevel 1 QOmega.I ^ 2 =
        twoLevel 0 1 qX * twoLevel 0 1 qK := by decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r16 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qK * oneLevel 1 QOmega.I ^ 3 =
        oneLevel 1 QOmega.I * twoLevel 0 1 qK * oneLevel 1 QOmega.I * twoLevel 0 1 qK := by
      decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r17 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qK * oneLevel 0 QOmega.I * oneLevel 1 QOmega.I =
        oneLevel 0 QOmega.I * oneLevel 1 QOmega.I * twoLevel 0 1 qK := by decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r18 j k hjk =>
    have key : twoLevel (0 : Fin 2) 1 qK ^ 2 * oneLevel 0 QOmega.I * oneLevel 1 QOmega.I = 1 := by
      decide +kernel
    simpa [mat, QOmega.toC_I] using congrArg (transferHom (injective_pair hjk.ne)) key
  | r19 j k l m hjk hlm hjl hkm hkl =>
    have key : twoLevel (0 : Fin 4) 1 qK * twoLevel 2 3 qK * twoLevel 0 2 qK * twoLevel 1 3 qK =
        twoLevel 0 2 qK * twoLevel 1 3 qK * twoLevel 0 1 qK * twoLevel 2 3 qK := by
      decide +kernel
    simpa [mat] using
      congrArg (transferHom (injective_four hjk.ne hjl.ne (hjk.trans hkm).ne hkl hkm.ne hlm.ne))
        key

/-- Remark 3.2: the relations of Figure 1 are sound for `Uₙ(ℤ[1/2, i])`. -/
theorem sound {w w' : Word (Gen n)} (h : Rel n w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w' :=
  lift_sem_eq (matOf_sound h)

/-- Every generator has an inverse modulo (1)–(3): `X⁻¹ = X`, `K⁻¹ = K⁷`,
`i⁻¹ = i³`. -/
theorem grouplike : Grouplike (Rel n) := by
  intro x
  cases x with
  | X j k h => exact ⟨X j k h, by simpa [pow_two] using Derivable.of (Rel.r2 j k h)⟩
  | K j k h => exact ⟨K j k h ^ 7, by simpa [← pow_succ] using Derivable.of (Rel.r3 j k h)⟩
  | i j => exact ⟨i j ^ 3, by simpa [← pow_succ] using Derivable.of (Rel.r1 j)⟩

end QCert.BianSelingerUn
