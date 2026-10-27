/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Powers labelled by `𝔽_d`

In a group, an element `g` with `g ^ d = 1` has well-defined powers labelled
by `ZMod d`: `g ^ k.val` behaves like `g ^ k` (Remark 6 of Appendix E of the
paper: exponents are computed modulo `d`).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Basic

namespace QCert.PhaseAffine

variable {G : Type*} [Group G] {d : ℕ} [NeZero d] {g : G}

omit [NeZero d] in
theorem pow_mod_eq (h : g ^ d = 1) (n : ℕ) : g ^ (n % d) = g ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n d, pow_add, pow_mul, h, one_pow, mul_one]

omit [NeZero d] in
theorem pow_val_natCast (h : g ^ d = 1) (n : ℕ) : g ^ (n : ZMod d).val = g ^ n := by
  rw [ZMod.val_natCast, pow_mod_eq h]

theorem pow_val_add (h : g ^ d = 1) (a b : ZMod d) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, pow_mod_eq h, pow_add]

omit [NeZero d] in
theorem pow_val_mul (h : g ^ d = 1) (a b : ZMod d) :
    g ^ (a * b).val = (g ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_eq h, pow_mul]

omit [NeZero d] in
theorem pow_val_zero : g ^ (0 : ZMod d).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem pow_val_neg (h : g ^ d = 1) (a : ZMod d) : g ^ (-a).val = (g ^ a.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_val_add h, neg_add_cancel, pow_val_zero]

omit [NeZero d] in
theorem pow_val_one (hd : 1 < d) : g ^ (1 : ZMod d).val = g := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hd, pow_one]

theorem pow_val_neg_one (h : g ^ d = 1) (hd : 1 < d) : g ^ (-1 : ZMod d).val = g⁻¹ := by
  rw [pow_val_neg h, pow_val_one hd]

theorem pow_val_sub (h : g ^ d = 1) (a b : ZMod d) :
    g ^ (a - b).val = g ^ a.val * (g ^ b.val)⁻¹ := by
  rw [sub_eq_add_neg, pow_val_add h, pow_val_neg h]

end QCert.PhaseAffine
