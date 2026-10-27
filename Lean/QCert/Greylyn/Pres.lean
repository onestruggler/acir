/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: calculating with the equations

Derivations from the equations of Table 3.1 are equalities in the monoid
`Pres n` of words modulo `≈` (`cl w = cl v ↔ w ≈ v`).  This file states
the equations there (`e1` … `e20`) and the inverses of the generators.
-/
import QCert.Greylyn.Syntax

namespace QCert.Greylyn

variable {n : ℕ}

/-- The monoid presented by the equations of Table 3.1. -/
abbrev Pres (n : ℕ) := (conGen (Rel n)).Quotient

/-- The class of a word. -/
def cl : Word (Gen n) →* Pres n := (conGen (Rel n)).mk'

theorem derivable_iff {w v : Word (Gen n)} : Derivable (Rel n) w v ↔ cl w = cl v :=
  (Con.eq _).symm

theorem cl_eq_of {w v : Word (Gen n)} (h : Rel n w v) : cl w = cl v :=
  derivable_iff.1 (Derivable.of h)

/-- `X_[j,k]`, `H_[j,k]`, `ω_[j]` in `Pres n`. -/
def gX (j k : Fin n) (h : j < k) : Pres n := cl (X j k h)
def gH (j k : Fin n) (h : j < k) : Pres n := cl (H j k h)
def gω (j : Fin n) : Pres n := cl (ω j)

theorem gX_congr {a b a' b' : Fin n} {h : a < b} {h' : a' < b'} (ea : a = a') (eb : b = b') :
    gX a b h = gX a' b' h' := by subst ea; subst eb; rfl

theorem gH_congr {a b a' b' : Fin n} {h : a < b} {h' : a' < b'} (ea : a = a') (eb : b = b') :
    gH a b h = gH a' b' h' := by subst ea; subst eb; rfl

@[simp] theorem cl_X (j k : Fin n) (h : j < k) : cl (X j k h) = gX j k h := rfl
@[simp] theorem cl_H (j k : Fin n) (h : j < k) : cl (H j k h) = gH j k h := rfl
@[simp] theorem cl_ω (j : Fin n) : cl (ω j) = gω j := rfl

section Relations

variable (j k l t : Fin n)

theorem e1 : gω j ^ 8 = 1 := by simpa using cl_eq_of (Rel.r1 j)
theorem e2 (h : j < k) : gH j k h * gH j k h = 1 := by
  simpa [pow_two] using cl_eq_of (Rel.r2 j k h)
theorem e3 (h : j < k) : gX j k h * gX j k h = 1 := by
  simpa [pow_two] using cl_eq_of (Rel.r3 j k h)
theorem e4 (h : j ≠ k) : gω j * gω k = gω k * gω j := by simpa using cl_eq_of (Rel.r4 j k h)
theorem e5 (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) : gω l * gH j k hjk = gH j k hjk * gω l := by
  simpa using cl_eq_of (Rel.r5 j k l hjk hlj hlk)
theorem e6 (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) : gω l * gX j k hjk = gX j k hjk * gω l := by
  simpa using cl_eq_of (Rel.r6 j k l hjk hlj hlk)
theorem e7 (hjk : j < k) (hlt : l < t) (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
    gH j k hjk * gH l t hlt = gH l t hlt * gH j k hjk := by
  simpa using cl_eq_of (Rel.r7 j k l t hjk hlt hlj hlk htj htk)
theorem e8 (hjk : j < k) (hlt : l < t) (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
    gH j k hjk * gX l t hlt = gX l t hlt * gH j k hjk := by
  simpa using cl_eq_of (Rel.r8 j k l t hjk hlt hlj hlk htj htk)
theorem e9 (hjk : j < k) (hlt : l < t) (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
    gX j k hjk * gX l t hlt = gX l t hlt * gX j k hjk := by
  simpa using cl_eq_of (Rel.r9 j k l t hjk hlt hlj hlk htj htk)
theorem e10 (h : j < k) : gX j k h * gω k = gω j * gX j k h := by
  simpa using cl_eq_of (Rel.r10 j k h)
theorem e11 (h : j < k) : gX j k h * gω j = gω k * gX j k h := by
  simpa using cl_eq_of (Rel.r11 j k h)
theorem e12 (hjk : j < k) (hkl : k < l) :
    gX j k hjk * gX j l (hjk.trans hkl) = gX k l hkl * gX j k hjk := by
  simpa using cl_eq_of (Rel.r12 j k l hjk hkl)
theorem e13 (hlj : l < j) (hjk : j < k) :
    gX j k hjk * gX l j hlj = gX l k (hlj.trans hjk) * gX j k hjk := by
  simpa using cl_eq_of (Rel.r13 j k l hlj hjk)
theorem e14 (hjk : j < k) (hkl : k < l) :
    gX j k hjk * gH j l (hjk.trans hkl) = gH k l hkl * gX j k hjk := by
  simpa using cl_eq_of (Rel.r14 j k l hjk hkl)
theorem e15 (hlj : l < j) (hjk : j < k) :
    gX j k hjk * gH l j hlj = gH l k (hlj.trans hjk) * gX j k hjk := by
  simpa using cl_eq_of (Rel.r15 j k l hlj hjk)
theorem e16 (h : j < k) : gω j * gω k * gX j k h = gX j k h * gω j * gω k := by
  simpa using cl_eq_of (Rel.r16 j k h)
theorem e17 (h : j < k) : gω j * gω k * gH j k h = gH j k h * gω j * gω k := by
  simpa using cl_eq_of (Rel.r17 j k h)
theorem e18 (h : j < k) : gH j k h * gX j k h = gω k ^ 4 * gH j k h := by
  simpa using cl_eq_of (Rel.r18 j k h)
theorem e19 (h : j < k) :
    gH j k h * gω j ^ 2 * gH j k h = gω j ^ 6 * gH j k h * gω j ^ 3 * gω k ^ 5 := by
  simpa using cl_eq_of (Rel.r19 j k h)
theorem e20 (hjk : j < k) (hkl : k < l) (hlt : l < t) :
    gH j k hjk * gH l t hlt * gH j l (hjk.trans hkl) * gH k t (hkl.trans hlt) =
      gH j l (hjk.trans hkl) * gH k t (hkl.trans hlt) * gH j k hjk * gH l t hlt := by
  simpa using cl_eq_of (Rel.r20 j k l t hjk hkl hlt)

end Relations

/-! ### Inverses and conjugation -/

theorem gω_pow_seven_mul (j : Fin n) : gω j ^ 7 * gω j = 1 := by
  rw [← pow_succ]; exact e1 j

theorem gω_mul_pow_seven (j : Fin n) : gω j * gω j ^ 7 = 1 := by
  rw [← pow_succ']; exact e1 j

/-- `x a = b x` with `x² = 1` gives `a = x b x`. -/
theorem eq_conj_of_comm {M : Type*} [Monoid M] {a b x : M} (hx : x * x = 1)
    (h : x * a = b * x) : a = x * b * x := by
  calc a = x * x * a := by rw [hx, one_mul]
    _ = x * b * x := by rw [mul_assoc, h, mul_assoc]

/-- `x b = a x` with `x² = 1` gives `a = x b x`. -/
theorem eq_conj_of_comm' {M : Type*} [Monoid M] {a b x : M} (hx : x * x = 1)
    (h : x * b = a * x) : a = x * b * x := by
  calc a = a * (x * x) := by rw [hx, mul_one]
    _ = x * b * x := by rw [← mul_assoc, h]

/-- Powers of `ω_[j]` are taken modulo 8. -/
theorem gω_pow_mod (j : Fin n) (e : ℕ) : gω j ^ e = gω j ^ (e % 8) := by
  conv_lhs => rw [← Nat.mod_add_div e 8, pow_add, pow_mul, e1, one_pow, mul_one]

end QCert.Greylyn
