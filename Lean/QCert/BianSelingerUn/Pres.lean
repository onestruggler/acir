/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: calculating with the relations

Derivations from the relations of Figure 1 are equalities in the monoid
`Pres n` of words modulo `∼_ℛ` (`cl w = cl v ↔ w ∼_ℛ v`).  This file states
the relations there (`e1` … `e19`) and the inverses of the generators.
-/
import QCert.BianSelingerUn.Syntax

namespace QCert.BianSelingerUn

variable {n : ℕ}

/-- The monoid presented by the relations of Figure 1. -/
abbrev Pres (n : ℕ) := (conGen (Rel n)).Quotient

/-- The class of a word. -/
def cl : Word (Gen n) →* Pres n := (conGen (Rel n)).mk'

theorem derivable_iff {w v : Word (Gen n)} : Derivable (Rel n) w v ↔ cl w = cl v :=
  (Con.eq _).symm

theorem cl_eq_of {w v : Word (Gen n)} (h : Rel n w v) : cl w = cl v :=
  derivable_iff.1 (Derivable.of h)

/-- `X_[j,k]`, `K_[j,k]`, `i_[j]` in `Pres n`. -/
def gX (j k : Fin n) (h : j < k) : Pres n := cl (X j k h)
def gK (j k : Fin n) (h : j < k) : Pres n := cl (K j k h)
def gi (j : Fin n) : Pres n := cl (i j)

theorem gX_congr {a b a' b' : Fin n} {h : a < b} {h' : a' < b'} (ea : a = a') (eb : b = b') :
    gX a b h = gX a' b' h' := by subst ea; subst eb; rfl

theorem gK_congr {a b a' b' : Fin n} {h : a < b} {h' : a' < b'} (ea : a = a') (eb : b = b') :
    gK a b h = gK a' b' h' := by subst ea; subst eb; rfl

@[simp] theorem cl_X (j k : Fin n) (h : j < k) : cl (X j k h) = gX j k h := rfl
@[simp] theorem cl_K (j k : Fin n) (h : j < k) : cl (K j k h) = gK j k h := rfl
@[simp] theorem cl_i (j : Fin n) : cl (i j) = gi j := rfl

section Relations

variable (j k l m : Fin n)

theorem e1 : gi j ^ 4 = 1 := by simpa using cl_eq_of (Rel.r1 j)
theorem e2 (h : j < k) : gX j k h * gX j k h = 1 := by
  simpa [pow_two] using cl_eq_of (Rel.r2 j k h)
theorem e3 (h : j < k) : gK j k h ^ 8 = 1 := by simpa using cl_eq_of (Rel.r3 j k h)
theorem e4 (h : j ≠ k) : gi j * gi k = gi k * gi j := by simpa using cl_eq_of (Rel.r4 j k h)
theorem e5 (hkl : k < l) (hjk : j ≠ k) (hjl : j ≠ l) : gi j * gX k l hkl = gX k l hkl * gi j := by
  simpa using cl_eq_of (Rel.r5 j k l hkl hjk hjl)
theorem e6 (hkl : k < l) (hjk : j ≠ k) (hjl : j ≠ l) : gi j * gK k l hkl = gK k l hkl * gi j := by
  simpa using cl_eq_of (Rel.r6 j k l hkl hjk hjl)
theorem e7 (hjk : j < k) (hlm : l < m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    gX j k hjk * gX l m hlm = gX l m hlm * gX j k hjk := by
  simpa using cl_eq_of (Rel.r7 j k l m hjk hlm hjl hjm hkl hkm)
theorem e8 (hjk : j < k) (hlm : l < m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    gX j k hjk * gK l m hlm = gK l m hlm * gX j k hjk := by
  simpa using cl_eq_of (Rel.r8 j k l m hjk hlm hjl hjm hkl hkm)
theorem e9 (hjk : j < k) (hlm : l < m) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    gK j k hjk * gK l m hlm = gK l m hlm * gK j k hjk := by
  simpa using cl_eq_of (Rel.r9 j k l m hjk hlm hjl hjm hkl hkm)
theorem e10 (h : j < k) : gi k * gX j k h = gX j k h * gi j := by
  simpa using cl_eq_of (Rel.r10 j k h)
theorem e11 (hjk : j < k) (hkl : k < l) :
    gX k l hkl * gX j k hjk = gX j k hjk * gX j l (hjk.trans hkl) := by
  simpa using cl_eq_of (Rel.r11 j k l hjk hkl)
theorem e12 (hjk : j < k) (hkl : k < l) :
    gX j l (hjk.trans hkl) * gX k l hkl = gX k l hkl * gX j k hjk := by
  simpa using cl_eq_of (Rel.r12 j k l hjk hkl)
theorem e13 (hjk : j < k) (hkl : k < l) :
    gK k l hkl * gX j k hjk = gX j k hjk * gK j l (hjk.trans hkl) := by
  simpa using cl_eq_of (Rel.r13 j k l hjk hkl)
theorem e14 (hjk : j < k) (hkl : k < l) :
    gK j l (hjk.trans hkl) * gX k l hkl = gX k l hkl * gK j k hjk := by
  simpa using cl_eq_of (Rel.r14 j k l hjk hkl)
theorem e15 (h : j < k) : gK j k h * gi k ^ 2 = gX j k h * gK j k h := by
  simpa using cl_eq_of (Rel.r15 j k h)
theorem e16 (h : j < k) : gK j k h * gi k ^ 3 = gi k * gK j k h * gi k * gK j k h := by
  simpa using cl_eq_of (Rel.r16 j k h)
theorem e17 (h : j < k) : gK j k h * gi j * gi k = gi j * gi k * gK j k h := by
  simpa using cl_eq_of (Rel.r17 j k h)
theorem e18 (h : j < k) : gK j k h ^ 2 * gi j * gi k = 1 := by
  simpa using cl_eq_of (Rel.r18 j k h)
theorem e19 (hjk : j < k) (hlm : l < m) (hjl : j < l) (hkm : k < m) (hkl : k ≠ l) :
    gK j k hjk * gK l m hlm * gK j l hjl * gK k m hkm =
      gK j l hjl * gK k m hkm * gK j k hjk * gK l m hlm := by
  simpa using cl_eq_of (Rel.r19 j k l m hjk hlm hjl hkm hkl)

end Relations

/-! ### Inverses and conjugation -/

theorem gK_pow_seven_mul (j k : Fin n) (h : j < k) : gK j k h ^ 7 * gK j k h = 1 := by
  rw [← pow_succ]; exact e3 j k h

theorem gK_mul_pow_seven (j k : Fin n) (h : j < k) : gK j k h * gK j k h ^ 7 = 1 := by
  rw [← pow_succ']; exact e3 j k h

theorem gi_pow_three_mul (j : Fin n) : gi j ^ 3 * gi j = 1 := by
  rw [← pow_succ]; exact e1 j

theorem gi_mul_pow_three (j : Fin n) : gi j * gi j ^ 3 = 1 := by
  rw [← pow_succ']; exact e1 j

/-- `a x = x b` with `x² = 1` gives `a = x b x`. -/
theorem eq_conj_of_comm {M : Type*} [Monoid M] {a b x : M} (hx : x * x = 1)
    (h : a * x = x * b) : a = x * b * x := by
  calc a = a * (x * x) := by rw [hx, mul_one]
    _ = x * b * x := by rw [← mul_assoc, h]

/-- Powers of `i_[j]` are taken modulo 4. -/
theorem gi_pow_mod (j : Fin n) (e : ℕ) : gi j ^ e = gi j ^ (e % 4) := by
  conv_lhs => rw [← Nat.mod_add_div e 4, pow_add, pow_mul, e1, one_pow, mul_one]

end QCert.BianSelingerUn
