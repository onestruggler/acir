/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Unit vectors over ℤ[1/√2]: least denominator exponents and residues

For a vector `v` with entries in `ℤ[1/√2]`, `lde v` is its least
denominator exponent (Definition 4.2 extended to vectors) and `num v i` the
numerator `√2^{lde v} vᵢ ∈ ℤ[√2]`.  For a unit vector:

* at a positive exponent some numerator is odd (by minimality), the number
  of odd numerators is even, and so is the number of odd numerators of each
  class (Lemma 5.13 of Amy et al.);
* at exponent `0` it is a signed basis vector `±e_a` (as in Lemma 5.14 of
  Amy et al.; Lemma 2.3 of Clément's notes).

States are the elements of `Oₙ(ℤ[1/√2])` (`O n`); their columns are unit
vectors, pairwise orthogonal.
-/
import QCert.HadamardPi.Arith

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

section Vectors

variable (v : Fin n → ℝ)

/-- Every entry of `v` is `u / √2^k` with `u ∈ ℤ[√2]`. -/
def DenV (k : ℕ) : Prop := ∀ i, Den k (v i)

/-- The entries lie in `ℤ[1/√2]`. -/
def InRing : Prop := ∀ i, v i ∈ ZInvSqrt2

/-- A unit vector. -/
def IsUnitVec : Prop := ∑ i, v i * v i = 1

variable {v}

theorem DenV.mono {k k' : ℕ} (hk : k ≤ k') (h : DenV v k) : DenV v k' := fun i => (h i).mono hk

theorem exists_denV (hv : InRing v) : ∃ k, DenV v k := by
  choose k hk using fun i => exists_den_of_mem (hv i)
  exact ⟨univ.sup k, fun i => (hk i).mono (le_sup (mem_univ i))⟩

variable (v)

/-- The least denominator exponent of a vector. -/
noncomputable def lde : ℕ := open Classical in if h : ∃ k, DenV v k then Nat.find h else 0

/-- The numerator of the `i`-th entry at the least denominator exponent. -/
noncomputable def num (i : Fin n) : ℤ√2 := numer (lde v) (v i)

variable {v}

theorem denV_lde (hv : InRing v) : DenV v (lde v) := by
  classical
  have h := exists_denV hv
  rw [lde, dif_pos h]; exact Nat.find_spec h

theorem lde_le {k : ℕ} (h : DenV v k) : lde v ≤ k := by
  classical
  rw [lde, dif_pos ⟨k, h⟩]; exact Nat.find_min' _ h

theorem toReal_num (hv : InRing v) (i : Fin n) :
    toReal (num v i) = Real.sqrt 2 ^ lde v * v i := toReal_numer (denV_lde hv i)

theorem num_eq (hv : InRing v) {u : Fin n → ℤ√2}
    (h : ∀ i, toReal (u i) = Real.sqrt 2 ^ lde v * v i) : num v = u :=
  funext fun i => numer_eq (h i)

theorem sum_num_sq (hv : InRing v) (hu : IsUnitVec v) :
    ∑ i, num v i * num v i = 2 ^ lde v := by
  apply toReal_injective
  rw [map_sum, map_pow, map_ofNat]
  simp only [map_mul, toReal_num hv]
  have : ∑ i, Real.sqrt 2 ^ lde v * v i * (Real.sqrt 2 ^ lde v * v i) =
      (Real.sqrt 2 ^ lde v) ^ 2 * ∑ i, v i * v i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, hu, mul_one, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]

/-- At a positive exponent some numerator is odd. -/
theorem exists_odd_num (hv : InRing v) (hk : 1 ≤ lde v) : ∃ i, Odd (num v i).re := by
  by_contra h
  push_neg at h
  have hd : DenV v (lde v - 1) := fun i => by
    refine den_pred (u := num v i) ?_ (Int.not_odd_iff_even.1 (h i))
    rw [toReal_num hv, Nat.sub_add_cancel hk]
  have := lde_le hd
  omega

/-- The odd numerators. -/
noncomputable def oddSet (v : Fin n → ℝ) : Finset (Fin n) :=
  open Classical in univ.filter fun i => Odd (num v i).re

theorem mem_oddSet {i : Fin n} : i ∈ oddSet v ↔ Odd (num v i).re := by
  classical
  simp [oddSet]

theorem even_card_oddSet (hv : InRing v) (hu : IsUnitVec v) (hk : 1 ≤ lde v) :
    Even (oddSet v).card := by
  classical
  have := even_card_odd_re (num v) hk (sum_num_sq hv hu)
  convert this using 2

theorem two_le_card_oddSet (hv : InRing v) (hu : IsUnitVec v) (hk : 1 ≤ lde v) :
    2 ≤ (oddSet v).card := by
  obtain ⟨i, hi⟩ := exists_odd_num hv hk
  have h1 : 1 ≤ (oddSet v).card := Finset.card_pos.2 ⟨i, mem_oddSet.2 hi⟩
  obtain ⟨c, hc⟩ := even_card_oddSet hv hu hk
  omega

/-- The odd numerators of class `1 + √2`. -/
theorem even_card_odd_odd_num (hv : InRing v) (hu : IsUnitVec v) :
    Even (univ.filter fun i => Odd (num v i).re ∧ Odd (num v i).im).card :=
  even_card_odd_odd (num v) (sum_num_sq hv hu)

/-- At exponent `0` a unit vector is a signed basis vector. -/
theorem eq_single_of_lde_zero (hv : InRing v) (hu : IsUnitVec v) (h0 : lde v = 0) :
    ∃ a : Fin n, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ v = Pi.single a ε := by
  classical
  have hs := (sum_sq_components (num v) (sum_num_sq hv hu)).1
  rw [h0, pow_zero] at hs
  set t : Fin n → ℤ := fun i => (num v i).re * (num v i).re + 2 * ((num v i).im * (num v i).im)
  have ht0 : ∀ i, 0 ≤ t i := fun i =>
    add_nonneg (mul_self_nonneg _) (mul_nonneg (by norm_num) (mul_self_nonneg _))
  have hs' : ∑ i, t i = 1 := hs
  have hv' : ∀ i, v i = (num v i).re + (num v i).im * Real.sqrt 2 := fun i => by
    have := toReal_num hv i; rw [h0, pow_zero, one_mul, toReal_apply] at this; exact this.symm
  -- some term is positive
  obtain ⟨a, ha⟩ : ∃ a, t a ≠ 0 := by
    by_contra hz; push Not at hz
    have : ∑ i, t i = 0 := Finset.sum_eq_zero fun i _ => hz i
    omega
  have hsplit := Finset.add_sum_erase univ t (mem_univ a)
  have hrest : 0 ≤ ∑ i ∈ univ.erase a, t i := Finset.sum_nonneg fun i _ => ht0 i
  have hta : t a = 1 := by have := ht0 a; omega
  have hz : ∀ i ∈ univ.erase a, t i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ht0 i).1 (by omega)
  -- the term at `a`
  have hima : (num v a).im = 0 := by
    have h1 : (num v a).im * (num v a).im ≤ 0 := by
      have := hta; simp only [t] at this; nlinarith [mul_self_nonneg (num v a).re]
    nlinarith [mul_self_nonneg (num v a).im]
  have hrea : (num v a).re * (num v a).re = 1 := by
    have := hta; simp only [t, hima] at this; linarith
  have hre : (num v a).re = 1 ∨ (num v a).re = -1 := by
    have h1 : (num v a).re ≤ 1 := by nlinarith
    have h2 : -1 ≤ (num v a).re := by nlinarith
    interval_cases h : (num v a).re <;> simp_all
  refine ⟨a, (num v a).re, ?_, ?_⟩
  · rcases hre with h | h <;> simp [h]
  · funext i
    by_cases hia : i = a
    · subst hia; rw [hv', hima]; simp
    · have hti := hz i (Finset.mem_erase.2 ⟨hia, mem_univ i⟩)
      simp only [t] at hti
      have h1 : (num v i).re * (num v i).re = 0 := by
        nlinarith [mul_self_nonneg (num v i).re, mul_self_nonneg (num v i).im]
      have h2 : (num v i).im * (num v i).im = 0 := by
        nlinarith [mul_self_nonneg (num v i).re, mul_self_nonneg (num v i).im]
      rw [hv', mul_self_eq_zero.1 h1, mul_self_eq_zero.1 h2]
      simp [hia]

end Vectors

section States

/-- The states: elements of `Oₙ(ℤ[1/√2])`. -/
abbrev O (n : ℕ) := ↥(O_ZInvSqrt2 n)

/-- The matrix of a state. -/
def mat (M : O n) : Matrix (Fin n) (Fin n) ℝ := ((M : unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

@[simp] theorem mat_mul (M N : O n) : mat (M * N) = mat M * mat N := rfl

@[simp] theorem mat_one : mat (1 : O n) = 1 := rfl

@[simp] theorem mat_sem (g : Gen n) : mat (sem n g) = genMat invSqrt2 g := rfl

theorem mat_injective : Function.Injective (mat (n := n)) := fun M N h =>
  Subtype.ext (Subtype.ext h)

theorem mat_lift (w : Word (Gen n)) : mat (FreeMonoid.lift (sem n) w) = wordMat invSqrt2 w :=
  lift_sem_val w

/-- The `j`-th column of a state. -/
def col (M : O n) (j : Fin n) : Fin n → ℝ := fun i => mat M i j

theorem col_inRing (M : O n) (j : Fin n) : InRing (col M j) := fun i => M.2 i j

theorem mat_transpose_mul (M : O n) : (mat M)ᵀ * mat M = 1 := by
  have h := (mem_unitaryGroup_iff'.1 M.1.2)
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

theorem col_dot (M : O n) (j j' : Fin n) :
    ∑ i, col M j i * col M j' i = if j = j' then 1 else 0 := by
  have h := congrFun (congrFun (mat_transpose_mul M) j) j'
  rw [mul_apply, one_apply] at h
  simpa [col] using h

theorem col_unit (M : O n) (j : Fin n) : IsUnitVec (col M j) := by
  have := col_dot M j j; rwa [if_pos rfl] at this

/-- The `j`-th column is the basis vector `e_j`. -/
def Fixed (M : O n) (j : Fin n) : Prop := col M j = Pi.single j 1

/-- A fixed column `j'` makes row `j'` vanish off the diagonal. -/
theorem mat_eq_zero_of_fixed {M : O n} {j j' : Fin n} (hf : Fixed M j') (h : j ≠ j') :
    mat M j' j = 0 := by
  have := col_dot M j' j
  rw [if_neg (Ne.symm h), hf] at this
  simpa [Pi.single_apply, col] using this

theorem eq_one_of_fixed {M : O n} (h : ∀ j, Fixed M j) : M = 1 := by
  apply mat_injective
  ext i j
  have := congrFun (h j) i
  simp only [col] at this
  rw [this, mat_one, one_apply, Pi.single_apply]

end States

end QCert.HadamardPi
