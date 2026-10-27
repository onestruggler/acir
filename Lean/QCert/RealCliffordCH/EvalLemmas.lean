/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Evaluation of shifted and padded circuits

General facts about `GateOps.eval`, the analogues for operators over any
commutative ring of `GateSem.sem_shift` and `GateSem.sem_pad`: a circuit
moved up one wire evaluates to its operator moved up (`eval_shift`), and a
circuit with idle wires on top to its operator on the bottom wires
(`eval_pad`).
-/
import QCert.Circuit.Eval

namespace QCert.RealCliffordCH

open Matrix

variable {Gate : ℕ → Type} {R : Type*} [CommRing R] {d : ℕ} (O : GateOps Gate R d)

theorem eval_of {n : ℕ} (g : Gen Gate n) : O.eval n (FreeMonoid.of g) = O.gen g :=
  FreeMonoid.lift_eval_of _ _

theorem eval_shift {n : ℕ} (w : Circuit Gate n) :
    O.eval (n + 1) (Circuit.shift w) = onTop 1 (O.eval n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onTop_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Circuit.shift_of, ih, map_mul (O.eval n), onTop_mul]
    rfl

theorem gen_pad (m : ℕ) {k : ℕ} (g : Gen Gate k) :
    O.gen (g.pad m) = onBottom (n := m) (O.gen g) := by
  induction g with
  | gate0 c =>
    show O.scalar c • (1 : Op R d _) = onBottom (O.scalar c • 1)
    rw [onBottom_smul, onBottom_one]
  | @gate1 n' c =>
    show onBottom (n := m + n') (O.gate1 c) = onBottom (n := m) (onBottom (n := n') (O.gate1 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate2 n' c =>
    show onBottom (n := m + n') (O.gate2 c) = onBottom (n := m) (onBottom (n := n') (O.gate2 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @gate3 n' c =>
    show onBottom (n := m + n') (O.gate3 c) = onBottom (n := m) (onBottom (n := n') (O.gate3 c))
    ext s t; rw [onBottom_onBottom_apply, onBottom_apply']; rfl
  | @up n' g ih =>
    show onTop 1 (O.gen (g.pad m)) = onBottom (n := m) (onTop 1 (O.gen g))
    rw [ih]; exact (onBottom_onTop _).symm

theorem eval_pad (m : ℕ) {k : ℕ} (w : Circuit Gate k) :
    O.eval (m + k) (Circuit.pad m w) = onBottom (n := m) (O.eval k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [onBottom_one]
  | mul_of g w ih =>
    rw [map_mul (Circuit.pad m), map_mul (O.eval _), ih, map_mul (O.eval k), onBottom_mul]
    congr 1
    show O.eval (m + k) (FreeMonoid.of (g.pad m)) = onBottom (O.eval k (FreeMonoid.of g))
    rw [eval_of O, eval_of O]; exact gen_pad O m g

end QCert.RealCliffordCH
