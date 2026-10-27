/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Every generator is invertible in the theory

Each gate of the phase-affine fragments has an inverse modulo the rules:
`X^{d-1}` from (1) and (3), `M_{a⁻¹}` from (1) and (2), `CX^{d-1}` from (1)
and (5), the crossing itself by the symmetry, and the powers `d - 1` of the
phase gates by (19), (20), (24), (31).
-/
import QCert.PhaseAffine.Soundness
import QCert.PhaseAffine.Derive

namespace QCert.PhaseAffine

variable {d lv : ℕ} [Fact d.Prime]

open Circuit

/-- Derivability is equality in the quotient monoid. -/
theorem derivable_iff_mk {X : Type*} {Γ : WRel X} {w v : Word X} :
    Derivable Γ w v ↔ (conGen Γ).mk' w = (conGen Γ).mk' v := (Con.eq _).symm

omit [Fact d.Prime] in
private theorem mk_rule {k : ℕ} (n : ℕ) {w v : C d lv k} (h : Rules d lv k w v) :
    (conGen (theory d lv (n + k))).mk' (pad n w) = (conGen (theory d lv (n + k))).mk' (pad n v) :=
  derivable_iff_mk.1 (Derivable.base n h)

theorem val_one_zmod : (1 : ZMod d).val = 1 :=
  ZMod.val_one_eq_one_mod d ▸ Nat.mod_eq_of_lt (Fact.out : d.Prime).one_lt

private theorem hd0 : d ≠ 0 := (Fact.out : d.Prime).ne_zero

/-- Every generator has a left inverse in the theory. -/
theorem grouplike (n : ℕ) : Grouplike (theory d lv n) := by
  intro x
  induction x with
  | @gate0 m g =>
    cases g with
    | omega h =>
      refine ⟨g0 (n := m) (Gate.omega h) ^ (d - 1), ?_⟩
      rw [pow_sub_one_mul hd0]
      simpa [map_pow, pad_g0] using Derivable.base m (Rules.r19 (d := d) h)
  | @gate1 m g =>
    cases g with
    | X =>
      refine ⟨g1 (n := m) Gate.X ^ᶠ (-1), derivable_iff_mk.2 ?_⟩
      have e3 := mk_rule m (Rules.r3 (d := d) (lv := lv) 1)
      have e1 := mk_rule m (Rules.r1 (d := d) (lv := lv))
      simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, pad_g1, Units.val_one,
        val_one_zmod, pow_one, map_one] at e3 e1
      rw [e1, mul_one] at e3
      simp only [fpow, map_mul, map_pow, map_one]
      exact ((Commute.self_pow _ _).eq).symm.trans e3
    | M a =>
      refine ⟨g1 (n := m) (Gate.M a⁻¹), derivable_iff_mk.2 ?_⟩
      have e2 := mk_rule m (Rules.r2 (d := d) (lv := lv) a a⁻¹)
      have e1 := mk_rule m (Rules.r1 (d := d) (lv := lv))
      simp only [seq_cons, seq_nil, one_mul, map_mul, pad_g1, mul_inv_cancel, map_one] at e2 e1
      rw [map_mul, e2, e1, map_one]
    | Z h =>
      refine ⟨g1 (n := m) (Gate.Z h) ^ (d - 1), ?_⟩
      rw [pow_sub_one_mul hd0]
      simpa [map_pow, pad_g1] using Derivable.base m (Rules.r20 (d := d) h)
    | S h =>
      refine ⟨g1 (n := m) (Gate.S h) ^ (d - 1), ?_⟩
      rw [pow_sub_one_mul hd0]
      simpa [map_pow, pad_g1] using Derivable.base m (Rules.r24 (d := d) h)
    | T h =>
      refine ⟨g1 (n := m) (Gate.T h) ^ (d - 1), ?_⟩
      rw [pow_sub_one_mul hd0]
      simpa [map_pow, pad_g1] using Derivable.base m (Rules.r31 (d := d) h)
  | @gate2 m g =>
    cases g with
    | CX =>
      refine ⟨g2 (n := m) Gate.CX ^ᶠ (-1), derivable_iff_mk.2 ?_⟩
      have e5 := mk_rule m (Rules.r5 (d := d) (lv := lv) 1)
      have e1 : (conGen (theory d lv (m + 2))).mk' (g1 (Gate.M 1)) = 1 := by
        simpa [pad_g1] using mk_rule (m + 1) (Rules.r1 (d := d) (lv := lv))
      simp only [seq_cons, seq_nil, one_mul, map_mul, fpow, map_pow, pad_g1, pad_g2,
        Units.val_one, map_one] at e5
      rw [e1, mul_one] at e5
      simpa [fpow] using e5
    | SWAP =>
      refine ⟨g2 (n := m) Gate.SWAP, ?_⟩
      simpa [seq, pad_g2] using Derivable.base m (Rules.swap_inv (d := d) (lv := lv))
  | gate3 g => nomatch g
  | @up m g ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨shift w, ?_⟩
    have := derivable_shift hw
    rwa [map_mul, map_one, shift_of] at this

end QCert.PhaseAffine
