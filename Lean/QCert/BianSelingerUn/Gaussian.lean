/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: denominator exponents over `GaussianInt`

§2.1: `γ = 1 + i` is a Gaussian prime; a Gaussian integer is *even* when
`γ` divides it (Definition 2.1), which is `re + im` even.  An element of
`𝔻[i] = ℤ[1/2, i]` is `w / γᵏ` for a Gaussian integer `w`; the least such
`k` is its least denominator exponent (Definition 2.4), here for vectors
(`HasNum v k w`: `γᵏ v = w`, and `lde v`).  For a unit vector with least
denominator exponent `k`, `Σ |wⱼ|² = 2ᵏ`, whence Lemmas 2.7 (`k = 0`: one
nonzero entry, a power of `i`) and 2.9 (`k > 0`: an even number of odd
entries).
-/
import QCert.BianSelingerUn.Semantics
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.IntervalCases

namespace QCert.BianSelingerUn

open Complex GaussianInt

/-- `γ = 1 + i ∈ GaussianInt`. -/
def γz : GaussianInt := ⟨1, 1⟩

/-- `i ∈ GaussianInt`. -/
def iz : GaussianInt := ⟨0, 1⟩

/-- A Gaussian integer is odd when `γ` does not divide it, i.e. `re + im` is
odd (Definition 2.1). -/
def GOdd (g : GaussianInt) : Prop := (g.re + g.im) % 2 = 1

instance (g : GaussianInt) : Decidable (GOdd g) := inferInstanceAs (Decidable (_ = _))

theorem γz_mul (c : GaussianInt) : γz * c = ⟨c.re - c.im, c.re + c.im⟩ := by
  ext <;> simp [γz] <;> ring

theorem iz_mul (c : GaussianInt) : iz * c = ⟨-c.im, c.re⟩ := by
  ext <;> simp [iz]

theorem γz_dvd_iff (g : GaussianInt) : γz ∣ g ↔ (g.re + g.im) % 2 = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [γz_mul]; simp only
    omega
  · intro h
    refine ⟨⟨(g.re + g.im) / 2, (g.im - g.re) / 2⟩, ?_⟩
    rw [γz_mul]
    ext <;> simp <;> omega

theorem not_GOdd_iff (g : GaussianInt) : ¬ GOdd g ↔ γz ∣ g := by
  rw [γz_dvd_iff, GOdd]; omega

theorem GOdd_iff (g : GaussianInt) : GOdd g ↔ ¬ γz ∣ g := by
  rw [← not_GOdd_iff, not_not]

theorem GOdd_neg (g : GaussianInt) : GOdd (-g) ↔ GOdd g := by
  simp only [GOdd, Zsqrtd.re_neg, Zsqrtd.im_neg]; omega

theorem GOdd_iz_mul (g : GaussianInt) : GOdd (iz * g) ↔ GOdd g := by
  simp only [GOdd, iz_mul]; omega

theorem GOdd_add (a b : GaussianInt) : GOdd (a + b) ↔ ¬ (GOdd a ↔ GOdd b) := by
  simp only [GOdd, Zsqrtd.re_add, Zsqrtd.im_add]; omega

theorem GOdd_sub (a b : GaussianInt) : GOdd (a - b) ↔ ¬ (GOdd a ↔ GOdd b) := by
  simp only [GOdd, Zsqrtd.re_sub, Zsqrtd.im_sub]; omega

theorem not_GOdd_γz_mul (c : GaussianInt) : ¬ GOdd (γz * c) := by
  rw [not_GOdd_iff]; exact dvd_mul_right _ _

/-- The norm of a Gaussian integer has the parity of the integer. -/
theorem norm_emod_two (g : GaussianInt) : g.norm % 2 = (g.re + g.im) % 2 := by
  rw [Zsqrtd.norm_def]
  have : g.re * g.re - -1 * g.im * g.im = g.re * g.re + g.im * g.im := by ring
  rw [this, Int.add_emod, Int.mul_emod, Int.mul_emod g.im, Int.add_emod g.re]
  rcases Int.emod_two_eq_zero_or_one g.re with h | h <;>
    rcases Int.emod_two_eq_zero_or_one g.im with h' | h' <;> simp [h, h']

noncomputable section

/-- `γ = 1 + i` in `ℂ`. -/
def γ : ℂ := 1 + I

theorem toComplex_γz : ((γz : GaussianInt) : ℂ) = γ := by
  simp [γz, γ, toComplex_def']

theorem toComplex_iz : ((iz : GaussianInt) : ℂ) = I := by
  simp [iz, toComplex_def']

theorem γ_ne_zero : γ ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [γ] at this

theorem γ_sq : γ ^ 2 = 2 * I := by
  rw [γ]; ring_nf; rw [I_sq]; ring

theorem normSq_γ : Complex.normSq γ = 2 := by
  simp [γ, Complex.normSq_apply]; norm_num

variable {n : ℕ}

/-- `v = w / γᵏ`: `w` is the numerator of `v` at the denominator exponent
`k` (Definition 2.4). -/
def HasNum (v : Fin n → ℂ) (k : ℕ) (w : Fin n → GaussianInt) : Prop :=
  ∀ j, γ ^ k * v j = (w j : ℂ)

theorem HasNum.unique {v : Fin n → ℂ} {k : ℕ} {w w' : Fin n → GaussianInt} (h : HasNum v k w)
    (h' : HasNum v k w') : w = w' := by
  funext j; exact toComplex_inj.1 ((h j).symm.trans (h' j))

theorem HasNum.succ {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w) :
    HasNum v (k + 1) (fun j => γz * w j) := by
  intro j; rw [pow_succ', mul_assoc, h j, toComplex_mul, toComplex_γz]

theorem HasNum.add_exp {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w) (d : ℕ) :
    HasNum v (k + d) (fun j => γz ^ d * w j) := by
  intro j; rw [pow_add, mul_comm (γ ^ k), mul_assoc, h j, toComplex_mul, map_pow, toComplex_γz]

theorem HasNum.pred {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v (k + 1) w)
    (c : Fin n → GaussianInt) (hc : ∀ j, w j = γz * c j) : HasNum v k c := by
  intro j
  have := h j
  rw [hc j, toComplex_mul, toComplex_γz, pow_succ', mul_assoc] at this
  exact mul_left_cancel₀ γ_ne_zero this

/-- Every element of `ℤ[1/2, i]` is `w / γᵏ`. -/
theorem exists_num_of_mem {z : ℂ} (hz : z ∈ ZHalfI) : ∃ (k : ℕ) (g : GaussianInt), γ ^ k * z = g := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · -- γ² / 2 = i
      refine ⟨2, iz, ?_⟩
      rw [toComplex_iz, γ_sq]; field_simp
    · exact ⟨0, iz, by simp [toComplex_iz]⟩
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, g, hg⟩ := hx
    obtain ⟨l, g', hg'⟩ := hy
    refine ⟨k + l, γz ^ l * g + γz ^ k * g', ?_⟩
    rw [toComplex_add, toComplex_mul, toComplex_mul, map_pow, map_pow, toComplex_γz, ← hg, ← hg']
    ring
  | neg x _ hx =>
    obtain ⟨k, g, hg⟩ := hx
    exact ⟨k, -g, by rw [toComplex_neg, ← hg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, g, hg⟩ := hx
    obtain ⟨l, g', hg'⟩ := hy
    refine ⟨k + l, g * g', ?_⟩
    rw [toComplex_mul, ← hg, ← hg']
    ring

/-- A vector with entries in `ℤ[1/2, i]` has a denominator exponent. -/
theorem exists_hasNum {v : Fin n → ℂ} (hv : ∀ j, v j ∈ ZHalfI) : ∃ k w, HasNum v k w := by
  choose k g hg using fun j => exists_num_of_mem (hv j)
  let K := Finset.univ.sup k
  refine ⟨K, fun j => γz ^ (K - k j) * g j, fun j => ?_⟩
  have hle : k j ≤ K := Finset.le_sup (Finset.mem_univ j)
  rw [toComplex_mul, map_pow, toComplex_γz, ← hg j, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hle]

open Classical in
/-- The least denominator exponent of a vector (Definition 2.4). -/
def lde (v : Fin n → ℂ) : ℕ :=
  if h : ∃ k w, HasNum v k w then Nat.find h else 0

theorem lde_spec {v : Fin n → ℂ} (h : ∃ k w, HasNum v k w) : ∃ w, HasNum v (lde v) w := by
  classical
  rw [lde, dif_pos h]; exact Nat.find_spec h

theorem lde_le {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w) : lde v ≤ k := by
  classical
  have h' : ∃ k w, HasNum v k w := ⟨k, w, h⟩
  rw [lde, dif_pos h']; exact Nat.find_min' h' ⟨w, h⟩

/-- At an exponent with an odd numerator entry, the exponent is the least
one. -/
theorem lde_eq {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    (hodd : k = 0 ∨ ∃ j, GOdd (w j)) : lde v = k := by
  apply le_antisymm (lde_le h)
  rcases hodd with rfl | ⟨j, hj⟩
  · exact Nat.zero_le _
  by_contra hlt
  push Not at hlt
  obtain ⟨w', hw'⟩ := lde_spec ⟨k, w, h⟩
  obtain ⟨d, hd⟩ : ∃ d, k = lde v + (d + 1) := ⟨k - lde v - 1, by omega⟩
  subst hd
  have := (hw'.add_exp (d + 1)).unique h
  have hwj : w j = γz ^ (d + 1) * w' j := (congrFun this j).symm
  rw [GOdd_iff, hwj] at hj
  exact hj (Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) _)

/-- At the least denominator exponent `k > 0`, some numerator entry is odd. -/
theorem exists_odd {v : Fin n → ℂ} {w : Fin n → GaussianInt} (h : HasNum v (lde v) w)
    (hk : 0 < lde v) : ∃ j, GOdd (w j) := by
  by_contra hno
  push Not at hno
  have hdiv : ∀ j, γz ∣ w j := fun j => (not_GOdd_iff _).1 (hno j)
  choose c hc using hdiv
  obtain ⟨k, hk'⟩ : ∃ k, lde v = k + 1 := ⟨lde v - 1, by omega⟩
  have h2 : HasNum v k c := (hk' ▸ h).pred c hc
  have := lde_le h2
  omega

/-- For a unit vector, `Σ |wⱼ|² = 2ᵏ`. -/
theorem sum_norm_eq {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → GaussianInt} (h : HasNum v k w) : ∑ j, (w j).norm = 2 ^ k := by
  have h1 : ∀ j, ((w j).norm : ℂ) = 2 ^ k * (star (v j) * v j) := by
    intro j
    rw [intCast_complex_norm, ← h j, map_mul, map_pow, normSq_γ, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    push_cast; ring
  have h2 : ((∑ j, (w j).norm : ℤ) : ℂ) = ((2 ^ k : ℤ) : ℂ) := by
    push_cast
    simp_rw [h1]
    rw [← Finset.mul_sum, hv, mul_one]
  exact_mod_cast h2

/-- A Gaussian integer of norm `1` is a power of `i`. -/
theorem eq_of_norm_eq_one {g : GaussianInt} (h : g.norm = 1) : g = 1 ∨ g = -iz ∨ g = -1 ∨ g = iz := by
  obtain ⟨a, b⟩ := g
  rw [Zsqrtd.norm_def] at h
  simp only at h
  have ha' : a * a ≤ 1 := by nlinarith [mul_self_nonneg b]
  have hb' : b * b ≤ 1 := by nlinarith [mul_self_nonneg a]
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> first | decide | omega

/-- The exponent `e` with `iᵉ u = 1`, for a power of `i`. -/
def expo (u : GaussianInt) : ℕ := if u = 1 then 0 else if u = -iz then 1 else if u = -1 then 2 else 3

theorem iz_pow_expo_mul {u : GaussianInt} (hu : u.norm = 1) : iz ^ expo u * u = 1 := by
  rcases eq_of_norm_eq_one hu with rfl | rfl | rfl | rfl <;> decide

/-- Lemma 2.7: a unit vector over `GaussianInt` has exactly one nonzero entry, a
power of `i`. -/
theorem unit_of_sum_norm_one {w : Fin n → GaussianInt} (h : ∑ j, (w j).norm = 1) :
    ∃ c, (w c).norm = 1 ∧ ∀ a, a ≠ c → w a = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, w c ≠ 0 := by
    by_contra hno
    push Not at hno
    simp [hno] at h
  have hpos : 1 ≤ (w c).norm := norm_pos.2 hc
  have hrest : (w c).norm + ∑ a ∈ Finset.univ.erase c, (w a).norm = 1 := by
    exact (Finset.add_sum_erase Finset.univ (fun a => (w a).norm) (Finset.mem_univ c)).trans h
  have hnn : ∀ a ∈ Finset.univ.erase c, 0 ≤ (w a).norm := fun a _ => GaussianInt.norm_nonneg _
  have hsum : ∑ a ∈ Finset.univ.erase c, (w a).norm = 0 := by
    have := Finset.sum_nonneg hnn
    omega
  refine ⟨c, ?_, fun a ha => ?_⟩
  · have := Finset.sum_nonneg hnn; omega
  · have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum a (Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩)
    exact norm_eq_zero.1 this

/-- The number of odd entries has the parity of `Σ |wⱼ|²`. -/
theorem sum_norm_emod_two (w : Fin n → GaussianInt) :
    (∑ j, (w j).norm) % 2 = ((Finset.univ.filter fun j => GOdd (w j)).card : ℤ) % 2 := by
  rw [Finset.sum_int_mod]
  have : ∀ j, (w j).norm % 2 = if GOdd (w j) then 1 else 0 := by
    intro j; rw [norm_emod_two]; unfold GOdd; split_ifs with h <;> omega
  simp_rw [this]
  rw [Finset.sum_boole]

/-- Lemma 2.9: at a positive exponent, a unit vector has an even number of
odd numerator entries. -/
theorem even_card_odd {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → GaussianInt} (h : HasNum v k w) (hk : 0 < k) :
    Even (Finset.univ.filter fun j => GOdd (w j)).card := by
  have h1 := sum_norm_emod_two w
  rw [sum_norm_eq hv h] at h1
  have h2 : (2 : ℤ) ^ k % 2 = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]; simp
  rw [h2] at h1
  rw [Nat.even_iff]
  omega

end

end QCert.BianSelingerUn
