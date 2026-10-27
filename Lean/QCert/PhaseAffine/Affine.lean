/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Affine relations on one and two wires

The rules of Figure 1 as equations in the group `Q d lv n`, on the bottom
wires of any circuit, and the first derived relations of Appendix D.1 of
Blake (arXiv:2603.06466): `X^d = id` (Lemma 17), `M_x X = X^x M_x`
(Lemma 18), `CX^d = id` (Lemma 19), and `X` on the target commutes with
`CX` (Lemma 21; here by conjugating (6) with `M_{-1}` on the control).
-/
import QCert.PhaseAffine.Calc
import QCert.PhaseAffine.Powers

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

theorem pad_shift (m : ℕ) {k : ℕ} (w : C d lv k) :
    pad m (shift w) = shift (pad m w) := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of x => rfl
  | mul x y hx hy => simp only [map_mul, hx, hy]

section Local

variable [Fact d.Prime] (m : ℕ)

theorem one_lt_d : 1 < d := (Fact.out : d.Prime).one_lt

/-! ### One wire -/

theorem rel1 : mk (g1 (n := m) (Gate.M (d := d) (lv := lv) 1)) = 1 := by
  simpa [pad_g1] using mk_rule m (Rules.r1 (d := d) (lv := lv))

theorem rel2 (x y : (ZMod d)ˣ) :
    mk (g1 (n := m) (Gate.M (lv := lv) y)) * mk (g1 (Gate.M x)) = mk (g1 (Gate.M (x * y))) := by
  simpa [pad_g1] using mk_rule m (Rules.r2 (d := d) (lv := lv) x y)

theorem relM_inv (x : (ZMod d)ˣ) :
    mk (g1 (n := m) (Gate.M (lv := lv) x)) = (mk (g1 (Gate.M x⁻¹)))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, rel2, inv_mul_cancel, rel1]

/-- Lemma 17: `X^d = id`. -/
theorem relXd : mk (g1 (n := m) (Gate.X (d := d) (lv := lv))) ^ d = 1 := by
  have e := mk_rule m (Rules.r3 (d := d) (lv := lv) 1)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, pad_g1, Units.val_one] at e
  rw [rel1, mul_one, ← pow_add] at e
  rwa [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (one_lt_d),
    Nat.add_sub_cancel' (one_lt_d (d := d)).le] at e

theorem relX_neg_one :
    mk (g1 (n := m) (Gate.X (d := d) (lv := lv))) ^ (-1 : ZMod d).val =
      (mk (g1 (Gate.X (d := d) (lv := lv))))⁻¹ :=
  pow_val_neg_one (relXd m) one_lt_d

/-- Lemma 18: `M_x X = X^x M_x`. -/
theorem relMX (x : (ZMod d)ˣ) :
    mk (g1 (n := m) (Gate.M (lv := lv) x)) * mk (g1 Gate.X) =
      mk (g1 Gate.X) ^ (x : ZMod d).val * mk (g1 (Gate.M x)) := by
  have e := mk_rule m (Rules.r3 (d := d) (lv := lv) x)
  simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, pad_g1] at e
  rw [relX_neg_one] at e
  exact (mul_inv_eq_iff_eq_mul.1 e).symm

/-! ### Two wires -/

omit [Fact d.Prime] in
theorem rel_comm (g h : Gate d lv 1) :
    mk (g1 (n := m + 1) g) * mk (shift (g1 (n := m) h)) = mk (shift (g1 h)) * mk (g1 g) := by
  rw [← map_mul, ← map_mul]; exact mk_comm1 g (g1 h)

/-- (4): `M_x` on the control, then `CX`, is `CX^x`, then `M_x`. -/
theorem rel4 (x : (ZMod d)ˣ) :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (shift (g1 (Gate.M x))) =
      mk (shift (g1 (Gate.M x))) * mk (g2 Gate.CX) ^ (x : ZMod d).val := by
  simpa [pad_g1, pad_g2, pad_shift, fpow] using mk_rule m (Rules.r4 (d := d) (lv := lv) x)

/-- (5) -/
theorem rel5 (x : (ZMod d)ˣ) :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) ^ (-(x : ZMod d)).val *
      mk (g1 (Gate.M x)) * mk (g2 Gate.CX) = mk (g1 (Gate.M x)) := by
  simpa [pad_g1, pad_g2, pad_shift, fpow, mul_assoc] using
    mk_rule m (Rules.r5 (d := d) (lv := lv) x)

/-- Lemma 19: `CX^d = id`. -/
theorem relCXd : mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) ^ d = 1 := by
  have e := rel5 m (d := d) (lv := lv) 1
  rw [show (g1 (Gate.M (d := d) (lv := lv) 1) : C d lv (m + 2)) = g1 (n := m + 1) (Gate.M 1)
    from rfl, rel1, mul_one, ← pow_succ] at e
  rwa [Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (one_lt_d), Nat.sub_add_cancel (one_lt_d (d := d)).le] at e

omit [Fact d.Prime] in
/-- (6): `X` on the control, then `CX`, is `CX`, then `X` on both wires. -/
theorem rel6 :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (shift (g1 Gate.X)) =
      mk (g1 Gate.X) * mk (shift (g1 Gate.X)) * mk (g2 Gate.CX) := by
  simpa [pad_g1, pad_g2, pad_shift, mul_assoc] using mk_rule m (Rules.r6 (d := d) (lv := lv))

/-- The crossing is an involution. -/
theorem relSW2 :
    mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))) * mk (g2 Gate.SWAP) = 1 := by
  simpa [pad_g2] using mk_rule m (Rules.swap_inv (d := d) (lv := lv))

theorem relSW_inv :
    (mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))))⁻¹ = mk (g2 Gate.SWAP) :=
  inv_eq_of_mul_eq_one_left (relSW2 m)

/-- The crossing is natural for one-wire gates. -/
theorem relSWnat (g : Gate d lv 1) :
    mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))) * mk (g1 g) =
      mk (shift (g1 g)) * mk (g2 Gate.SWAP) := by
  simpa [pad_g1, pad_g2, pad_shift] using mk_rule m (Rules.swap_nat1 (d := d) (lv := lv) g)

theorem relSWnat' (g : Gate d lv 1) :
    mk (g2 (n := m) (Gate.SWAP (d := d) (lv := lv))) * mk (shift (g1 g)) =
      mk (g1 g) * mk (g2 Gate.SWAP) := by
  have e := relSWnat m g
  calc _ = mk (g2 Gate.SWAP) * (mk (shift (g1 g)) * mk (g2 Gate.SWAP)) * (mk (g2 Gate.SWAP))⁻¹ := by
          group
    _ = _ := by rw [← e, relSW_inv]; simp only [mul_assoc, relSW2 m, mul_one]; rw [← mul_assoc,
          relSW2 m, one_mul]

theorem mk_shift_one {n : ℕ} {w : C d lv n} (h : mk w = 1) : mk (shift w) = 1 := by
  rw [show (1 : Q d lv (n + 1)) = mk (shift (1 : C d lv n)) by simp]
  exact mk_shift (by rw [h, map_one])

theorem relM1_sq :
    mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) * mk (g1 (Gate.M (-1))) = 1 := by
  rw [rel2, show (-1 : (ZMod d)ˣ) * -1 = 1 by simp, rel1]

theorem relM1_top_sq :
    mk (shift (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1)))) *
      mk (shift (g1 (Gate.M (-1)))) = 1 := by
  have := mk_shift_one (w := g1 (n := m) (Gate.M (d := d) (lv := lv) (-1)) * g1 (Gate.M (-1)))
    (by rw [map_mul, relM1_sq])
  simpa only [map_mul] using this

/-- Conjugating by `M_{-1}` on the control inverts `CX`. -/
theorem relM1CX :
    mk (shift (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1)))) * mk (g2 Gate.CX) *
      mk (shift (g1 (Gate.M (-1)))) = (mk (g2 Gate.CX))⁻¹ := by
  have e := rel4 m (d := d) (lv := lv) (-1)
  have hM := relM1_top_sq m (d := d) (lv := lv)
  rw [Units.val_neg, Units.val_one, pow_val_neg_one (relCXd m) one_lt_d] at e
  rw [mul_assoc, e, ← mul_assoc, hM, one_mul]

/-- Conjugating by `M_{-1}` inverts `X`. -/
theorem relM1X :
    mk (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))) * mk (g1 Gate.X) *
      mk (g1 (Gate.M (-1))) = (mk (g1 Gate.X))⁻¹ := by
  rw [relMX, Units.val_neg, Units.val_one, relX_neg_one, mul_assoc, relM1_sq, mul_one]

/-- Lemma 21: `X` on the target commutes with `CX`. -/
theorem rel21 :
    mk (g2 (n := m) (Gate.CX (d := d) (lv := lv))) * mk (g1 Gate.X) =
      mk (g1 Gate.X) * mk (g2 Gate.CX) := by
  -- conjugate (6) by `M_{-1}` on the control
  set c := mk (g2 (n := m) (Gate.CX (d := d) (lv := lv)))
  set xb := mk (g1 (n := m + 1) (Gate.X (d := d) (lv := lv)))
  set xt := mk (shift (g1 (n := m) (Gate.X (d := d) (lv := lv))))
  set mt := mk (shift (g1 (n := m) (Gate.M (d := d) (lv := lv) (-1))))
  have h6 : c * xt = xb * xt * c := rel6 m
  have hc : mt * c * mt = c⁻¹ := relM1CX m
  have hx : mt * xt * mt = xt⁻¹ := by
    have := mk_shift_one (w := g1 (n := m) (Gate.M (d := d) (lv := lv) (-1)) * g1 Gate.X *
      g1 (Gate.M (-1)) * g1 Gate.X) (by rw [map_mul, map_mul, map_mul, relM1X, inv_mul_cancel])
    simp only [map_mul] at this
    exact eq_inv_of_mul_eq_one_left this
  have hb : mt * xb = xb * mt := by
    simp only [mt, xb]
    exact (rel_comm m _ _).symm
  have hmm : mt * mt = 1 := relM1_top_sq m
  have hbt : xb * xt = xt * xb := by
    simp only [xb, xt]; exact rel_comm m _ _
  -- conjugating h6: `c⁻¹ xt⁻¹ = xb xt⁻¹ c⁻¹`
  have h6' : c⁻¹ * xt⁻¹ = xb * xt⁻¹ * c⁻¹ := by
    rw [← hc, ← hx]
    calc mt * c * mt * (mt * xt * mt) = mt * (c * xt) * mt := by
          simp only [mul_assoc, ← mul_assoc mt mt, hmm, one_mul]
      _ = mt * (xb * xt * c) * mt := by rw [h6]
      _ = xb * (mt * xt * mt) * (mt * c * mt) := by
          simp only [mul_assoc]
          rw [← mul_assoc mt xb, hb]
          simp only [mul_assoc, ← mul_assoc mt mt, hmm, one_mul]
  -- invert: `xt c = c xt xb⁻¹`
  have h7 : xt * c = c * xt * xb⁻¹ := by
    have := congrArg (·⁻¹) h6'
    simp only [mul_inv_rev, inv_inv] at this
    rw [this]; group
  -- combine
  have : xt * (c * xb) = xt * (xb * c) := by
    calc xt * (c * xb) = c * xt := by rw [← mul_assoc, h7]; group
      _ = xb * xt * c := h6
      _ = xt * (xb * c) := by rw [hbt, mul_assoc]
  exact mul_left_cancel this

end Local

end QCert.PhaseAffine
