/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Calculating in the theory

The circuits of `n` wires modulo the theory form a group `Q d lv n` (every
generator being invertible, `grouplike`); `mk` sends a circuit to its class,
and two circuits are derivably equal exactly when their classes are equal.
This file collects the structural facts used by the normal-form proofs:
gates on disjoint wires commute (for whole circuits shifted up), the scalar
is central, rules apply on the bottom wires of any circuit, and
derivations move up a wire.
-/
import QCert.PhaseAffine.Grouplike

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

/-- The circuits of `n` wires modulo the theory. -/
abbrev Q (d lv n : ℕ) := (conGen (theory d lv n)).Quotient

/-- The class of a circuit. -/
abbrev mk {n : ℕ} : C d lv n →* Q d lv n := (conGen (theory d lv n)).mk'

theorem mk_eq_iff {n : ℕ} {w v : C d lv n} : mk w = mk v ↔ Derivable (theory d lv n) w v :=
  derivable_iff_mk.symm

theorem mk_surjective {n : ℕ} : Function.Surjective (mk : C d lv n → Q d lv n) :=
  fun q => Con.mk'_surjective q

/-- A rule on the bottom wires. -/
theorem mk_rule {k : ℕ} (m : ℕ) {w v : C d lv k} (h : Rules d lv k w v) :
    mk (pad m w) = mk (pad m v) :=
  mk_eq_iff.2 (Derivable.base m h)

/-- An equation moved up one wire. -/
theorem mk_shift {n : ℕ} {w v : C d lv n} (h : mk w = mk v) :
    mk (shift w) = mk (shift v) :=
  mk_eq_iff.2 (derivable_shift (mk_eq_iff.1 h))

/-- A structural rule. -/
theorem mk_lift {n : ℕ} {w v : C d lv n} (h : Lift (Padded (Rules d lv)) n w v) : mk w = mk v :=
  mk_eq_iff.2 (Derivable.of h)

section Group

variable [Fact d.Prime]

theorem exists_left_inv {n : ℕ} (q : Q d lv n) : ∃ r, r * q = 1 := by
  obtain ⟨w, rfl⟩ := mk_surjective q
  induction w using FreeMonoid.inductionOn with
  | one => exact ⟨1, by simp⟩
  | of x =>
    obtain ⟨u, hu⟩ := grouplike (d := d) (lv := lv) n x
    exact ⟨mk u, by rw [← map_mul, mk_eq_iff.2 hu, map_one]⟩
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨b * a, by rw [map_mul, mul_assoc, ← mul_assoc a, ha, one_mul, hb]⟩

/-- The circuits modulo the theory form a group. -/
noncomputable instance instGroupQ {n : ℕ} : Group (Q d lv n) :=
  { (inferInstance : Monoid (Q d lv n)) with
    inv := fun q => Classical.choose (exists_left_inv q)
    inv_mul_cancel := fun q => Classical.choose_spec (exists_left_inv q) }

end Group

/-! ### Structural facts -/

theorem mk_comm1 {n : ℕ} (h : Gate d lv 1) (u : C d lv n) :
    mk (g1 h * shift u) = mk (shift u * g1 h) := by
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x => rw [shift_of]; exact (mk_lift (Lift.comm1 h x)).symm
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem mk_comm2 {n : ℕ} (h : Gate d lv 2) (u : C d lv n) :
    mk (g2 h * shift (shift u)) = mk (shift (shift u) * g2 h) := by
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x => rw [shift_of, shift_of]; exact (mk_lift (Lift.comm2 h x)).symm
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem mk_comm3 {n : ℕ} (h : Gate d lv 3) (u : C d lv n) :
    mk (g3 h * shift (shift (shift u))) = mk (shift (shift (shift u)) * g3 h) := by
  induction u using FreeMonoid.inductionOn with
  | one => simp
  | of x => rw [shift_of, shift_of, shift_of]; exact (mk_lift (Lift.comm3 h x)).symm
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

/-- The scalar is the same on every wire. -/
theorem mk_scalar_up {n : ℕ} (c : Gate d lv 0) :
    mk (shift (g0 (n := n) c)) = mk (g0 (n := n + 1) c) :=
  mk_lift (Lift.scalar c)

/-- Two scalars commute: there is one scalar gate. -/
theorem gate0_eq (c c' : Gate d lv 0) : c = c' := by
  cases c; cases c'; rfl

/-- The scalar is central. -/
theorem mk_scalar_comm {n : ℕ} (c : Gate d lv 0) (x : Gen (Gate d lv) n) :
    mk (g0 c * FreeMonoid.of x) = mk (FreeMonoid.of x * g0 c) := by
  induction x with
  | gate0 c' => rw [gate0_eq c c']
  | @gate1 m h =>
    rw [map_mul, map_mul, ← mk_scalar_up c, ← map_mul, ← map_mul]
    exact (mk_comm1 h (g0 c)).symm
  | @gate2 m h =>
    have e : mk (shift (shift (g0 (n := m) c))) = mk (g0 (n := m + 2) c) := by
      rw [mk_shift (mk_scalar_up c), mk_scalar_up c]
    rw [map_mul, map_mul, ← e, ← map_mul, ← map_mul]
    exact (mk_comm2 h (g0 c)).symm
  | @gate3 m h =>
    have e : mk (shift (shift (shift (g0 (n := m) c)))) = mk (g0 (n := m + 3) c) := by
      rw [mk_shift (mk_shift (mk_scalar_up c)), mk_shift (mk_scalar_up c), mk_scalar_up c]
    rw [map_mul, map_mul, ← e, ← map_mul, ← map_mul]
    exact (mk_comm3 h (g0 c)).symm
  | @up m g ih =>
    rw [map_mul, map_mul, ← mk_scalar_up c, ← map_mul, ← map_mul, ← shift_of, ← map_mul,
      ← map_mul]
    exact mk_shift ih

theorem mk_scalar_comm_word {n : ℕ} (c : Gate d lv 0) (w : C d lv n) :
    mk (g0 c * w) = mk (w * g0 c) := by
  induction w using FreeMonoid.inductionOn with
  | one => simp
  | of x => exact mk_scalar_comm c x
  | mul x y hx hy =>
    simp only [map_mul] at hx hy ⊢
    rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

end QCert.PhaseAffine
