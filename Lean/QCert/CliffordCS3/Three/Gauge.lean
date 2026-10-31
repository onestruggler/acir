/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A two-state coset action with a central correction

Changing the odd-coset representative introduces one central factor each
time two odd letters have been read. For even words this factor depends
only on their number of odd letters, independently of the starting coset.
-/
import QCert.CliffordCS3.Three.QuotientGroup
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

namespace QCert.CliffordCS3.Three.Gauge

def bit (c : Bool) : Nat := if c then 1 else 0
def next (c p : Bool) : Bool := xor c p
def carry (c p : Bool) : Nat := bit (c && p)

theorem bit_bound (c : Bool) : bit c ≤ 1 := by cases c <;> decide

theorem bit_carry (c p : Bool) : bit (next c p) + 2 * carry c p = bit c + bit p := by
  cases c <;> cases p <;> decide

variable {X : Type*}

def finish (odd : X → Bool) (c : Bool) : List X → Bool
  | [] => c
  | x :: xs => finish odd (next c (odd x)) xs

def turns (odd : X → Bool) (c : Bool) : List X → Nat
  | [] => 0
  | x :: xs => carry c (odd x) + turns odd (next c (odd x)) xs

def count (odd : X → Bool) : List X → Nat
  | [] => 0
  | x :: xs => bit (odd x) + count odd xs

theorem count_eq (odd : X → Bool) (c : Bool) (xs : List X) :
    bit (finish odd c xs) + 2 * turns odd c xs = bit c + count odd xs := by
  induction xs generalizing c with
  | nil => simp only [finish, turns, count, mul_zero, add_zero]
  | cons x xs ih =>
    have hi := ih (next c (odd x))
    have hb := bit_carry c (odd x)
    simp only [finish, turns, count]
    omega

theorem even_finish (odd : X → Bool) (c : Bool) (xs : List X) (k : Nat)
    (hk : count odd xs = 2 * k) : finish odd c xs = c ∧ turns odd c xs = k := by
  have he := count_eq odd c xs
  rw [hk] at he
  have hb := bit_bound (finish odd c xs)
  cases c with
  | false =>
    cases hf : finish odd false xs with
    | false =>
      refine ⟨rfl, ?_⟩
      simp [hf, bit] at he
      omega
    | true =>
      simp [hf, bit] at he
      omega
  | true =>
    cases hf : finish odd true xs with
    | false =>
      simp [hf, bit] at he
      omega
    | true =>
      refine ⟨rfl, ?_⟩
      simp [hf, bit] at he
      omega

section Group
variable {G : Type*} [Group G]

def eval (L : X → G) (xs : List X) : G := (xs.map L).prod

def run (odd : X → Bool) (H : Bool → X → G) (c : Bool) : List X → G
  | [] => 1
  | x :: xs => H c x * run odd H (next c (odd x)) xs

theorem commute_eval (r : G) (L : X → G) (hr : ∀ x, Commute r (L x)) (xs : List X) :
    Commute r (eval L xs) := by
  induction xs with
  | nil => exact Commute.one_right _
  | cons x xs ih => exact (hr x).mul_right ih

/-- The letter-level gauge equation telescopes over every word. -/
theorem run_eq (C r : G) (L : X → G) (odd : X → Bool) (H : Bool → X → G)
    (hrC : Commute r C) (hrL : ∀ x, Commute r (L x))
    (hH : ∀ c x, H c x =
      C ^ bit c * L x * (C ^ bit (next c (odd x)))⁻¹ * r ^ carry c (odd x))
    (c : Bool) (xs : List X) :
    run odd H c xs = C ^ bit c * eval L xs * (C ^ bit (finish odd c xs))⁻¹ * r ^ turns odd c xs := by
  induction xs generalizing c with
  | nil => simp only [run, eval, List.map_nil, List.prod_nil, finish, turns, pow_zero,
      mul_one, mul_inv_cancel]
  | cons x xs ih =>
    rw [run, hH, ih]
    have hr : Commute (r ^ carry c (odd x))
        (C ^ bit (next c (odd x)) * eval L xs * (C ^ bit (finish odd (next c (odd x)) xs))⁻¹) :=
      (((hrC.pow_right _).mul_right (commute_eval r L hrL xs)).mul_right
        (hrC.pow_right _).inv_right).pow_left _
    simp only [eval, List.map_cons, List.prod_cons, finish, turns] at *
    calc
      _ = (C ^ bit c * L x * (C ^ bit (next c (odd x)))⁻¹) *
          (r ^ carry c (odd x) *
            (C ^ bit (next c (odd x)) * (List.map L xs).prod *
              (C ^ bit (finish odd (next c (odd x)) xs))⁻¹)) *
          r ^ turns odd (next c (odd x)) xs := by group
      _ = (C ^ bit c * L x * (C ^ bit (next c (odd x)))⁻¹) *
          ((C ^ bit (next c (odd x)) * (List.map L xs).prod *
              (C ^ bit (finish odd (next c (odd x)) xs))⁻¹) * r ^ carry c (odd x)) *
          r ^ turns odd (next c (odd x)) xs := by rw [hr.eq]
      _ = C ^ bit c * (L x * (List.map L xs).prod) *
          (C ^ bit (finish odd (next c (odd x)) xs))⁻¹ *
          r ^ (carry c (odd x) + turns odd (next c (odd x)) xs) := by rw [pow_add]; group

/-- An even word has the same correction exponent in either coset. -/
theorem run_even (C r : G) (L : X → G) (odd : X → Bool) (H : Bool → X → G)
    (hrC : Commute r C) (hrL : ∀ x, Commute r (L x))
    (hH : ∀ c x, H c x =
      C ^ bit c * L x * (C ^ bit (next c (odd x)))⁻¹ * r ^ carry c (odd x))
    (c : Bool) (xs : List X) (k : Nat) (hk : count odd xs = 2 * k) :
    run odd H c xs = C ^ bit c * eval L xs * (C ^ bit c)⁻¹ * r ^ k := by
  rw [run_eq C r L odd H hrC hrL hH]
  obtain ⟨hf, ht⟩ := even_finish odd c xs k hk
  rw [hf, ht]

/-- Equal lifted even words with the same odd-letter count have equal residuals. -/
theorem run_eq_of_even (C r : G) (L : X → G) (odd : X → Bool) (H : Bool → X → G)
    (hrC : Commute r C) (hrL : ∀ x, Commute r (L x))
    (hH : ∀ c x, H c x =
      C ^ bit c * L x * (C ^ bit (next c (odd x)))⁻¹ * r ^ carry c (odd x))
    (c : Bool) (xs ys : List X) (k : Nat)
    (hx : count odd xs = 2 * k) (hy : count odd ys = 2 * k)
    (he : eval L xs = eval L ys) : run odd H c xs = run odd H c ys := by
  rw [run_even C r L odd H hrC hrL hH c xs k hx,
    run_even C r L odd H hrC hrL hH c ys k hy, he]

end Group
end QCert.CliffordCS3.Three.Gauge
