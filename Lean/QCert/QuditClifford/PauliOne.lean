/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# One qudit, modulo the scalars: the Pauli calculus

Proposition 4.8 on one wire, in the group `Gs p g 1` of one-wire circuits
modulo the rules and the scalars.  From `H⁴ = 1`, (C1), (C5), the
definitions (T2), (T3) of `X`, `Z` and (T1) of `M_1`, `M_{-1}` together
with (C3) at `k = 0` (`(S H)³ = 1`) and (C2) (`H² = Z⁻¹ X S⁻¹ H S⁻¹ H S⁻¹ H`):

* `H X H⁻¹ = Z` and `H Z H⁻¹ = X⁻¹`;
* `S Z = Z S` and `S X S⁻¹ = X Z`;
* `Z X = X Z` and `X^p = Z^p = 1`.

The derivations are carried out in an arbitrary group from those
relations (section `OneAlg`), then instantiated.  Every identity was
checked on the matrices for `p = 3, 5, 7` first.
-/
import QCert.QuditClifford.Projective

namespace QCert.QuditClifford

/-- Normalisation of words in a group: numeral powers expanded, products
associated to the right, inverses distributed and adjacent inverse letters
cancelled. -/
syntax "gnorm" : tactic

macro_rules
  | `(tactic| gnorm) => `(tactic| simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_rev,
      inv_inv, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel, mul_one,
      inv_one])

/-! ### The derivations, in any group -/

section OneAlg

variable {G : Type*} [Group G] {h s x z : G}

theorem h4_e (h4 : h ^ 4 = 1) : h * (h * (h * h)) = 1 := by
  rw [← h4]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem h4_y (h4 : h ^ 4 = 1) (y : G) : h * (h * (h * (h * y))) = y := by
  calc h * (h * (h * (h * y))) = (h * (h * (h * h))) * y := by simp only [mul_assoc]
    _ = y := by rw [h4_e h4, one_mul]

theorem h4_inv (h4 : h ^ 4 = 1) : h⁻¹ = h * (h * h) :=
  inv_eq_of_mul_eq_one_left (by rw [mul_assoc, mul_assoc]; exact h4_e h4)

/-- `gnorm` modulo `h⁴ = 1`, given the proof of `h⁴ = 1`: inverses of `h` are
cubes, and four consecutive letters `h` cancel. -/
syntax "gnorm4" term : tactic

macro_rules
  | `(tactic| gnorm4 $h) => `(tactic| simp only [pow_succ, pow_zero, one_mul, mul_assoc,
      mul_inv_rev, inv_inv, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel,
      mul_one, inv_one, h4_inv $h, h4_y $h, h4_e $h])

theorem h4_sq_inv (h4 : h ^ 4 = 1) : (h ^ 2)⁻¹ = h ^ 2 :=
  inv_eq_of_mul_eq_one_left (by gnorm4 h4)

/-- (C5) with `S` inverted. -/
theorem one_c5inv (h4 : h ^ 4 = 1) (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s) :
    s * (h ^ 2 * s⁻¹ * h ^ 2) = (h ^ 2 * s⁻¹ * h ^ 2) * s := by
  have hc : Commute s (h ^ 2 * s * h ^ 2) := by
    show s * (h ^ 2 * s * h ^ 2) = (h ^ 2 * s * h ^ 2) * s
    simpa only [mul_assoc] using c5
  have e : (h ^ 2 * s * h ^ 2)⁻¹ = h ^ 2 * s⁻¹ * h ^ 2 :=
    inv_eq_of_mul_eq_one_right (by gnorm4 h4)
  rw [← e]
  exact hc.inv_right.eq

theorem one_F1 (hx : x = h * s * h ^ 2 * s⁻¹ * h) (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) :
    h * x * h⁻¹ = z := by
  rw [hx, hz]; gnorm

theorem one_F1' (hx : x = h * s * h ^ 2 * s⁻¹ * h) (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) :
    x = h⁻¹ * z * h := by
  rw [← one_F1 hx hz]; gnorm

theorem one_F2 (h4 : h ^ 4 = 1) (hx : x = h * s * h ^ 2 * s⁻¹ * h)
    (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) : h * z * h⁻¹ = x⁻¹ := by
  rw [hx, hz]; gnorm4 h4

theorem one_F3 (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹)
    (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s) : s * z = z * s := by
  calc s * z = (s * h ^ 2 * s * h ^ 2) * s⁻¹ := by rw [hz]; gnorm
    _ = (h ^ 2 * s * h ^ 2 * s) * s⁻¹ := by rw [c5]
    _ = z * s := by rw [hz]; gnorm

theorem one_r1' (r1 : s * h * s * h * s * h = 1) : s * h * s * h = h⁻¹ * s⁻¹ := by
  calc s * h * s * h = (s * h * s * h * s * h) * (h⁻¹ * s⁻¹) := by gnorm
    _ = h⁻¹ * s⁻¹ := by rw [r1, one_mul]

theorem one_F4 (h4 : h ^ 4 = 1) (hx : x = h * s * h ^ 2 * s⁻¹ * h)
    (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s)
    (r1 : s * h * s * h * s * h = 1) : s * x * s⁻¹ = x * z := by
  have r1' := one_r1' r1
  have e1 : s * x = h⁻¹ * s⁻¹ * (h * s⁻¹ * h) := by
    calc s * x = (s * h * s * h) * (h * s⁻¹ * h) := by rw [hx]; gnorm
      _ = _ := by rw [r1']
  have e2 : x * z * s = h⁻¹ * s⁻¹ * (h * s⁻¹ * h) := by
    calc x * z * s = h * (s * (h ^ 2 * s⁻¹ * h ^ 2)) * h * s * h ^ 2 := by rw [hx, hz]; gnorm
      _ = h * ((h ^ 2 * s⁻¹ * h ^ 2) * s) * h * s * h ^ 2 := by rw [one_c5inv h4 c5]
      _ = h ^ 3 * s⁻¹ * h ^ 2 * (s * h * s * h) * h := by gnorm
      _ = h ^ 3 * s⁻¹ * h ^ 2 * (h⁻¹ * s⁻¹) * h := by rw [r1']
      _ = _ := by gnorm4 h4
  calc s * x * s⁻¹ = x * z * s * s⁻¹ := by rw [e1, e2]
    _ = x * z := by gnorm

theorem one_F4' (h4 : h ^ 4 = 1) (hx : x = h * s * h ^ 2 * s⁻¹ * h)
    (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s)
    (r1 : s * h * s * h * s * h = 1) : s⁻¹ * x * s = x * z⁻¹ := by
  have f3 := one_F3 hz c5
  have f4 := one_F4 h4 hx hz c5 r1
  have f4' : x * z * s = s * x := by rw [← f4]; gnorm
  calc s⁻¹ * x * s = s⁻¹ * x * (s * z) * z⁻¹ := by gnorm
    _ = s⁻¹ * (x * z * s) * z⁻¹ := by rw [f3]; gnorm
    _ = x * z⁻¹ := by rw [f4']; gnorm

theorem one_F5 (h4 : h ^ 4 = 1) (hx : x = h * s * h ^ 2 * s⁻¹ * h)
    (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s)
    (r1 : s * h * s * h * s * h = 1) (r2 : h ^ 2 = z⁻¹ * x * s⁻¹ * h * s⁻¹ * h * s⁻¹ * h) :
    z * x = x * z := by
  have r2' : z⁻¹ * x = h * s * h⁻¹ * s * h⁻¹ * s := by
    calc z⁻¹ * x = (z⁻¹ * x * s⁻¹ * h * s⁻¹ * h * s⁻¹ * h) * (h⁻¹ * s * h⁻¹ * s * h⁻¹ * s) := by
          gnorm
      _ = h ^ 2 * (h⁻¹ * s * h⁻¹ * s * h⁻¹ * s) := by rw [← r2]
      _ = _ := by gnorm
  have rsh : s * h * s = h⁻¹ * s⁻¹ * h⁻¹ := by
    calc s * h * s = (s * h * s * h * s * h) * (h⁻¹ * s⁻¹ * h⁻¹) := by gnorm
      _ = _ := by rw [r1, one_mul]
  have key : (z * x)⁻¹ * (x * z) = 1 := by
    calc (z * x)⁻¹ * (x * z) = x⁻¹ * (z⁻¹ * x) * z := by gnorm
      _ = x⁻¹ * (h * s * h⁻¹ * s * h⁻¹ * s) * z := by rw [r2']
      _ = h⁻¹ * (s * h * s) * h⁻¹ * s * h ^ 2 * s * h ^ 2 * s⁻¹ := by
          rw [hx, hz]; gnorm4 h4
      _ = h⁻¹ * (h⁻¹ * s⁻¹ * h⁻¹) * h⁻¹ * s * h ^ 2 * s * h ^ 2 * s⁻¹ := by rw [rsh]
      _ = h ^ 2 * s⁻¹ * (h ^ 2 * (s * h ^ 2 * s * h ^ 2)) * s⁻¹ := by
          gnorm4 h4
      _ = h ^ 2 * s⁻¹ * (h ^ 2 * (h ^ 2 * s * h ^ 2 * s)) * s⁻¹ := by rw [c5]
      _ = 1 := by gnorm4 h4
  exact inv_mul_eq_one.1 key

theorem one_zpow {n : ℕ} (h4 : h ^ 4 = 1) (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹)
    (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s) (sn : s ^ n = 1) : z ^ n = 1 := by
  have hc0 : Commute s (h ^ 2 * s * h ^ 2) := by
    show s * (h ^ 2 * s * h ^ 2) = (h ^ 2 * s * h ^ 2) * s
    simpa only [mul_assoc] using c5
  have hc : Commute (h ^ 2 * s * h ^ 2) s⁻¹ := hc0.symm.inv_right
  have e : (h ^ 2 * s * h ^ 2) ^ n = 1 := by
    rw [show h ^ 2 * s * h ^ 2 = (h ^ 2)⁻¹ * s * h ^ 2 by rw [h4_sq_inv h4], conj_pow_inv, sn,
      mul_one, inv_mul_cancel]
  rw [hz, hc.mul_pow, e, one_mul, inv_pow, sn, inv_one]

theorem one_xpow {n : ℕ} (h4 : h ^ 4 = 1) (hx : x = h * s * h ^ 2 * s⁻¹ * h)
    (hz : z = h ^ 2 * s * h ^ 2 * s⁻¹) (c5 : s * h ^ 2 * s * h ^ 2 = h ^ 2 * s * h ^ 2 * s)
    (sn : s ^ n = 1) : x ^ n = 1 := by
  rw [one_F1' hx hz, conj_pow_inv, one_zpow h4 hz c5 sn, mul_one, inv_mul_cancel]

end OneAlg

/-! ### One wire modulo the scalars -/

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-- `H`, `S`, `X`, `Z` modulo the rules and the scalars. -/
local notation "𝐇" => qs p g 1 H
local notation "𝐒" => qs p g 1 S
local notation "𝐗" => qs p g 1 (X p)
local notation "𝐙" => qs p g 1 (Z p)

theorem qs_rule1 {w v : Circ 1} (h : Rule p g 1 w v) : qs p g 1 w = qs p g 1 v := by
  have := qs_rule (g := g) 0 h
  rwa [pad_zero_one, pad_zero_one] at this

theorem qsH_pow_four : 𝐇 ^ 4 = 1 := by
  have := qs_eq_of_derives (g := g) (H_pow_four p (OddGen.hp2 g) g OddGen.hg 0)
  rwa [map_pow, map_one] at this

theorem qsS_pow_p : 𝐒 ^ p = 1 := by
  rw [← map_pow, qs_rule1 Rule.C1, map_one]

theorem qsX_eq : 𝐗 = 𝐇 * 𝐒 * 𝐇 ^ 2 * 𝐒⁻¹ * 𝐇 := by
  simp only [X, seq_def, map_mul, map_pow]
  rw [pow_pred_eq_inv qsS_pow_p]
  simp only [mul_assoc]

theorem qsZ_eq : 𝐙 = 𝐇 ^ 2 * 𝐒 * 𝐇 ^ 2 * 𝐒⁻¹ := by
  simp only [Z, seq_def, map_mul, map_pow]
  rw [pow_pred_eq_inv qsS_pow_p]
  simp only [mul_assoc]

theorem qs_C5 : 𝐒 * 𝐇 ^ 2 * 𝐒 * 𝐇 ^ 2 = 𝐇 ^ 2 * 𝐒 * 𝐇 ^ 2 * 𝐒 := by
  have h := qs_rule1 (g := g) Rule.C5
  simp only [seq_def, map_mul, map_pow] at h
  simpa only [mul_assoc] using h

/-- `(S H)³ = 1` modulo the scalars: (C3) at `k = 0` is `M_1 = 1`, and
(T1) at `a = 1` is `(S H)³` times scalars. -/
theorem qs_R1 : 𝐒 * 𝐇 * 𝐒 * 𝐇 * 𝐒 * 𝐇 = 1 := by
  have h := qs_rule1 (g := g) (Rule.C3 0)
  simp only [ZMod.val_zero, pow_zero, map_one] at h
  have e : qs p g 1 (M p 1) = 𝐒 * 𝐇 * 𝐒 * 𝐇 * 𝐒 * 𝐇 := by
    simp only [M, seq_def, map_mul, map_pow, qs_neg1, qs_ω, one_pow, one_mul, inv_one,
      sub_self, zero_div, ZMod.val_zero, pow_zero, mul_one]
    rw [pow_val_one qsS_pow_p]
    simp only [mul_assoc]
  rw [← e, ← h]

theorem qsZ_pow_p : 𝐙 ^ p = 1 := one_zpow qsH_pow_four qsZ_eq qs_C5 qsS_pow_p

theorem qsX_pow_p : 𝐗 ^ p = 1 := one_xpow qsH_pow_four qsX_eq qsZ_eq qs_C5 qsS_pow_p

/-- (C2) with (T1) at `a = -1`, modulo the scalars. -/
theorem qs_R2 : 𝐇 ^ 2 = 𝐙⁻¹ * 𝐗 * 𝐒⁻¹ * 𝐇 * 𝐒⁻¹ * 𝐇 * 𝐒⁻¹ * 𝐇 := by
  have h := qs_rule1 (g := g) Rule.C2
  simp only [seq_def, map_mul, map_pow, qs_neg1, one_pow, one_mul] at h
  rw [h]
  have two : (2 : ZMod p) ≠ 0 := two_ne_zero_p g
  have e1 : ((1 : ZMod p) - -1) / 2 = 1 := by rw [sub_neg_eq_add, one_add_one_eq_two, div_self two]
  have e2 : ((1 : ZMod p) - -1) / (2 * -1) = -1 := by
    rw [sub_neg_eq_add, one_add_one_eq_two, mul_neg_one, div_neg, div_self two]
  simp only [M, seq_def, map_mul, map_pow, qs_neg1, qs_ω, one_pow, one_mul]
  rw [e1, e2, inv_neg, inv_one, pow_val_neg qsS_pow_p, pow_val_neg qsZ_pow_p, pow_val_one qsS_pow_p,
    pow_val_one qsZ_pow_p, pow_val_one qsX_pow_p]
  simp only [mul_assoc]

/-! ### The one-wire Pauli calculus -/

theorem qs_HXH : 𝐇 * 𝐗 * 𝐇⁻¹ = 𝐙 := one_F1 qsX_eq qsZ_eq

theorem qs_HZH : 𝐇 * 𝐙 * 𝐇⁻¹ = 𝐗⁻¹ := one_F2 qsH_pow_four qsX_eq qsZ_eq

theorem qs_SZ : 𝐒 * 𝐙 = 𝐙 * 𝐒 := one_F3 qsZ_eq qs_C5

theorem qs_SXS : 𝐒 * 𝐗 * 𝐒⁻¹ = 𝐗 * 𝐙 := one_F4 qsH_pow_four qsX_eq qsZ_eq qs_C5 qs_R1

theorem qs_SXS' : 𝐒⁻¹ * 𝐗 * 𝐒 = 𝐗 * 𝐙⁻¹ := one_F4' qsH_pow_four qsX_eq qsZ_eq qs_C5 qs_R1

theorem qs_ZX : 𝐙 * 𝐗 = 𝐗 * 𝐙 := one_F5 qsH_pow_four qsX_eq qsZ_eq qs_C5 qs_R1 qs_R2

theorem qs_X_eq_conj : 𝐗 = 𝐇⁻¹ * 𝐙 * 𝐇 := one_F1' qsX_eq qsZ_eq

theorem qs_HSH : 𝐇 ^ 2 * 𝐒 * (𝐇 ^ 2)⁻¹ = 𝐙 * 𝐒 := by
  rw [h4_sq_inv qsH_pow_four, qsZ_eq]; gnorm

end QCert.QuditClifford
