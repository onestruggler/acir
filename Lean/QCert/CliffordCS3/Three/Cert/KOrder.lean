/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The K-order axiom from both cosets

The transported atom-cube equation and the defining fourth power of CS
prove both residual equations of K^8 = 1.
-/
import QCert.CliffordCS3.Three.Conjugation
import QCert.CliffordCS3.Three.Checks
import Mathlib.Algebra.Group.Commute.Units

namespace QCert.CliffordCS3.Three.Cert.KOrder

open Swap01

private theorem rotate_power {M : Type*} [Monoid M] (a b : M) (n : ℕ) :
    a * (b * a) ^ n = (a * b) ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ← mul_assoc, ih]

private theorem ab_order {M : Type*} [Monoid M] (a p : M)
    (ha : a ^ 3 = p ^ 2) (hp : p ^ 4 = 1) :
    (a * (a ^ 2 * p)) ^ 4 = 1 := by
  have h : a * (a ^ 2 * p) = p ^ 3 := by
    rw [← mul_assoc, ← pow_succ', ha, ← pow_succ]
  rw [h, ← pow_mul]
  calc
    p ^ (3 * 4) = (p ^ 4) ^ 3 := by rw [← pow_mul]
    _ = 1 := by rw [hp]; simp

private theorem ba_order {M : Type*} [Monoid M] (a p : M)
    (ha : a ^ 3 = p ^ 2) (hp : p ^ 4 = 1) :
    (a ^ 2 * p * a) ^ 4 = 1 := by
  have ha6 : a ^ 6 = 1 := by
    calc
      a ^ 6 = (a ^ 3) ^ 2 := by rw [← pow_mul]
      _ = (p ^ 2) ^ 2 := by rw [ha]
      _ = 1 := by rw [← pow_mul]; exact hp
  apply (IsUnit.of_pow_eq_one ha6 (by decide)).mul_left_cancel
  rw [rotate_power a (a ^ 2 * p) 4, ab_order a p ha hp]
  simp

theorem false_order : Derivable Rel ((Cert.atom * (Cert.atom ^ 2 * phase)) ^ 4) 1 := by
  apply of_q
  simp only [map_pow, map_mul, map_one]
  have ha := q_of atom_cube
  have hp := q_of (Derivable.of (Rel.c5 1))
  simp only [map_pow] at ha
  simp only [map_pow, map_one] at hp
  exact ab_order (q Cert.atom) (q phase) ha hp

theorem true_order : Derivable Rel ((Cert.atom ^ 2 * phase * Cert.atom) ^ 4) 1 := by
  apply of_q
  simp only [map_pow, map_mul, map_one]
  have ha := q_of atom_cube
  have hp := q_of (Derivable.of (Rel.c5 1))
  simp only [map_pow] at ha
  simp only [map_pow, map_one] at hp
  exact ba_order (q Cert.atom) (q phase) ha hp

def falseRule : Rule Rel := Rule.ofDerivable _ _ false_order
def trueRule : Rule Rel := Rule.ofDerivable _ _ true_order

end QCert.CliffordCS3.Three.Cert.KOrder
