/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# ℤ[√2], ℤ[1/√2] and least denominator exponents

Definitions 4.1 and 4.2 of Hadamard-Π: every `x ∈ ℤ[1/√2]` is `u / √2^k`
with `u ∈ ℤ[√2]` (`Den k x`); the least such `k` is the least denominator
exponent.  We write `u = a + b√2` (`u.re = a`, `u.im = b`): `u` is *odd*
when `a` is odd, i.e. `u ≡ 1` or `u ≡ 1 + √2 (mod 2)`, and its *class* is
the parity of `b`.

The parity facts behind Lemma 5.13 of Amy et al. (quoted as Lemma 4.6 of
Hadamard-Π, and as Lemma 2.1 in Clément's notes): if `Σ uᵢ² = 2^k` with
`k ≥ 1`, an even number of the `uᵢ` are odd, and an even number are odd
of each class.
-/
import QCert.HadamardPi.Local
import Mathlib.Data.ZMod.Basic

namespace QCert.HadamardPi

open Matrix Finset

/-! ### ℤ√2 inside ℝ -/

theorem toReal_apply (u : ℤ√2) : toReal u = u.re + u.im * Real.sqrt 2 := by
  simp [toReal]

theorem toReal_injective : Function.Injective toReal := by
  refine Zsqrtd.lift_injective _ fun n h => ?_
  have h1 : n ≤ 1 := by nlinarith
  have h2 : -1 ≤ n := by nlinarith
  interval_cases n <;> omega

theorem sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

/-- `x = u / √2^k` for some `u ∈ ℤ[√2]`. -/
def Den (k : ℕ) (x : ℝ) : Prop := ∃ u : ℤ√2, toReal u = Real.sqrt 2 ^ k * x

theorem Den.succ {k : ℕ} {x : ℝ} (h : Den k x) : Den (k + 1) x := by
  obtain ⟨u, hu⟩ := h
  exact ⟨rt2 * u, by rw [map_mul, toReal_rt2, hu, pow_succ]; ring⟩

theorem Den.mono {k k' : ℕ} {x : ℝ} (hk : k ≤ k') (h : Den k x) : Den k' x := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.succ

theorem Den.add {k : ℕ} {x y : ℝ} (hx : Den k x) (hy : Den k y) : Den k (x + y) := by
  obtain ⟨u, hu⟩ := hx; obtain ⟨w, hw⟩ := hy
  exact ⟨u + w, by rw [map_add, hu, hw]; ring⟩

theorem Den.neg {k : ℕ} {x : ℝ} (hx : Den k x) : Den k (-x) := by
  obtain ⟨u, hu⟩ := hx
  exact ⟨-u, by rw [map_neg, hu]; ring⟩

theorem Den.sub {k : ℕ} {x y : ℝ} (hx : Den k x) (hy : Den k y) : Den k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem Den.mul {k k' : ℕ} {x y : ℝ} (hx : Den k x) (hy : Den k' y) : Den (k + k') (x * y) := by
  obtain ⟨u, hu⟩ := hx; obtain ⟨w, hw⟩ := hy
  exact ⟨u * w, by rw [map_mul, hu, hw, pow_add]; ring⟩

theorem den_zero (k : ℕ) : Den k 0 := ⟨0, by simp⟩

theorem den_one : Den 0 1 := ⟨1, by simp⟩

theorem den_intCast (k : ℕ) (z : ℤ) : Den k z :=
  Den.mono (Nat.zero_le k) ⟨z, by simp⟩

theorem den_invSqrt2 : Den 1 invSqrt2 := ⟨1, by rw [map_one, pow_one, sqrt2_mul_invSqrt2]⟩

/-- Every element of `ℤ[1/√2]` has a denominator exponent. -/
theorem exists_den_of_mem {x : ℝ} (hx : x ∈ ZInvSqrt2) : ∃ k, Den k x := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨1, den_invSqrt2⟩
  | zero => exact ⟨0, den_zero 0⟩
  | one => exact ⟨0, den_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx; obtain ⟨k', hk'⟩ := hy
    exact ⟨max k k', (hk.mono (le_max_left _ _)).add (hk'.mono (le_max_right _ _))⟩
  | neg x _ hx => obtain ⟨k, hk⟩ := hx; exact ⟨k, hk.neg⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx; obtain ⟨k', hk'⟩ := hy
    exact ⟨k + k', hk.mul hk'⟩

/-- The numerator of `x` at the exponent `k`. -/
noncomputable def numer (k : ℕ) (x : ℝ) : ℤ√2 :=
  open Classical in if h : Den k x then h.choose else 0

theorem toReal_numer {k : ℕ} {x : ℝ} (h : Den k x) :
    toReal (numer k x) = Real.sqrt 2 ^ k * x := by
  rw [numer, dif_pos h]; exact h.choose_spec

theorem numer_eq {k : ℕ} {x : ℝ} {u : ℤ√2} (h : toReal u = Real.sqrt 2 ^ k * x) :
    numer k x = u :=
  toReal_injective (by rw [toReal_numer ⟨u, h⟩, h])

/-- `x = √2^k x'`: real numbers of the form `toReal u` at exponent `k`. -/
theorem eq_of_numer {k : ℕ} {x : ℝ} (h : Den k x) :
    x = toReal (numer k x) / Real.sqrt 2 ^ k := by
  rw [toReal_numer h]; field_simp

/-- `√2 (a + b√2) = 2b + a√2`. -/
theorem rt2_mul (w : ℤ√2) : rt2 * w = ⟨2 * w.im, w.re⟩ := by
  ext <;> simp [rt2]

/-- A numerator with even rational part is divisible by `√2`, so the
exponent drops by one. -/
theorem den_pred {k : ℕ} {x : ℝ} {u : ℤ√2} (h : toReal u = Real.sqrt 2 ^ (k + 1) * x)
    (he : Even u.re) : Den k x := by
  obtain ⟨c, hc⟩ := he
  refine ⟨⟨u.im, c⟩, ?_⟩
  have hu : u = rt2 * ⟨u.im, c⟩ := by rw [rt2_mul]; ext <;> simp [hc]; ring
  rw [hu, map_mul, toReal_rt2, pow_succ] at h
  have h0 := sqrt2_ne_zero
  apply mul_left_cancel₀ h0
  rw [h]; ring

/-! ### Real and irrational parts of sums -/

/-- The rational part, as an additive map. -/
def reHom : ℤ√2 →+ ℤ := AddMonoidHom.mk' Zsqrtd.re Zsqrtd.re_add

/-- The irrational part, as an additive map. -/
def imHom : ℤ√2 →+ ℤ := AddMonoidHom.mk' Zsqrtd.im Zsqrtd.im_add

theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ√2) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum reHom f s

theorem im_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ√2) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum imHom f s

/-! ### Parities -/

theorem intCast_zmod2 (x : ℤ) : (x : ZMod 2) = if Odd x then 1 else 0 := by
  rcases Int.even_or_odd x with h | h
  · rw [if_neg (Int.not_odd_iff_even.2 h)]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).2 (even_iff_two_dvd.1 h)
  · rw [if_pos h]
    obtain ⟨c, rfl⟩ := h
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring

/-- If the integers `f i` sum to an even number, an even number of them
are odd. -/
theorem even_card_odd {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (h : (∑ i, (f i : ZMod 2)) = 0) :
    Even (univ.filter fun i => Odd (f i)).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← h]
  simp only [intCast_zmod2]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

variable {n : ℕ}

/-- The two equations of `Σ uᵢ² = 2^k` in the basis `1, √2`. -/
theorem sum_sq_components (u : Fin n → ℤ√2) {k : ℕ} (h : ∑ i, u i * u i = 2 ^ k) :
    ∑ i, ((u i).re * (u i).re + 2 * ((u i).im * (u i).im)) = 2 ^ k ∧
      ∑ i, (u i).re * (u i).im = 0 := by
  have hre := congrArg Zsqrtd.re h
  have him := congrArg Zsqrtd.im h
  rw [re_sum] at hre; rw [im_sum] at him
  have h2 : ((2 : ℤ√2) ^ k) = ((2 ^ k : ℤ) : ℤ√2) := by push_cast; rfl
  rw [h2, Zsqrtd.re_intCast] at hre
  rw [h2, Zsqrtd.im_intCast] at him
  constructor
  · rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    simp [Zsqrtd.re_mul]; ring
  · have : ∑ i, (u i * u i).im = 2 * ∑ i, (u i).re * (u i).im := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp [Zsqrtd.im_mul]; ring
    rw [this] at him; omega

/-- Lemma 5.13 of Amy et al.: at a positive exponent, a unit vector has an
even number of odd numerators. -/
theorem even_card_odd_re (u : Fin n → ℤ√2) {k : ℕ} (hk : 1 ≤ k) (h : ∑ i, u i * u i = 2 ^ k) :
    Even (univ.filter fun i => Odd (u i).re).card := by
  have h1 := (sum_sq_components u h).1
  have hodd : ∀ i, Odd ((u i).re * (u i).re) ↔ Odd (u i).re := fun i => Int.odd_mul.trans (and_self_iff)
  have := even_card_odd (fun i => (u i).re * (u i).re) (by
    have h' := congrArg (fun z : ℤ => (z : ZMod 2)) h1
    simp only [Int.cast_sum, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h'
    rw [show (2 : ZMod 2) = 0 from rfl, zero_pow (by omega)] at h'
    simpa using h')
  simpa only [hodd] using this

/-- Lemma 5.13 of Amy et al.: an even number of numerators are odd with an
odd irrational part (class `1 + √2`). -/
theorem even_card_odd_odd (u : Fin n → ℤ√2) {k : ℕ} (h : ∑ i, u i * u i = 2 ^ k) :
    Even (univ.filter fun i => Odd (u i).re ∧ Odd (u i).im).card := by
  have h1 := (sum_sq_components u h).2
  have := even_card_odd (fun i => (u i).re * (u i).im) (by
    have h' := congrArg (fun z : ℤ => (z : ZMod 2)) h1
    simpa using h')
  simpa only [Int.odd_mul] using this

end QCert.HadamardPi
