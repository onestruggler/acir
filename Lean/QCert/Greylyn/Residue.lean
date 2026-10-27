/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: residues in `ℤ[ω]` for the proof of the Main Lemma

Facts about `ℤ[ω]` modulo powers of `δ` used in the proof of Lemma 31.

* `ℤ[ω]` is a domain (it embeds in `ℂ`), and `2 = δ⁴ u₂` for a unit `u₂`
  (Example 8: `2 = δ⁴ ω⁻² λ⁻²`).
* Divisibility by `δ²` and `δ³` read off the residues `a + b + c + d`,
  `b + d`, `c + d` (`δz_sq_dvd_iff`, `δz_pow_three_dvd_iff`).
* The residue `m` of Lemma 11 (`x ≡ ωᵐ (mod δ³)`) is multiplicative
  (`res_mul`), so a unit factor does not change the exponent `z` of a
  syllable (`zexp_mul_left`); and adding `δ²` adds `2` to it.
* What `H` does to two entries (Convention 2's computations in Cases 1 and
  3): for two odd entries whose residues differ by an odd number, both
  `(x ± y)/δ` are odd with the same residue (`pair_oo_odd`, Subcases 1.2,
  1.3); for residues differing by `2`, both `(x ± y)/δ²` are odd with
  residues differing by `2` (`pair_oo_two`, Subcase 1.4); for one odd and
  one even entry, `x ± y` are odd with the same residue (`pair_oe`,
  Subcase 1.5); and for two even entries, `x ± y` are divisible by `δ³`,
  or by exactly `δ²` or `δ` with odd quotients of the same residue
  (`pair_ee`, Subcases 1.6.1–1.6.3).
-/
import QCert.Greylyn.ZOmega

namespace QCert.Greylyn

namespace ZOmega

/-! ### `ℤ[ω]` is a domain -/

instance : Nontrivial ZOmega := ⟨⟨0, 1, by decide⟩⟩

instance : NoZeroDivisors ZOmega where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have h' : toC x * toC y = 0 := by rw [← map_mul, h, map_zero]
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact Or.inl (eq_zero_of_toC h1)
    · exact Or.inr (eq_zero_of_toC h1)

instance : IsDomain ZOmega := NoZeroDivisors.to_isDomain _

theorem δz_mul_cancel {a b : ZOmega} (h : δz * a = δz * b) : a = b :=
  mul_left_cancel₀ δz_ne_zero h

/-- `2 = δ⁴ u₂`, `u₂ = ω⁻² λ⁻² = ω⁶ (√2 - 1)²`. -/
def u2 : ZOmega := ωz ^ 6 * (s2z - 1) ^ 2

theorem two_eq_δz_pow_four : (1 + 1 : ZOmega) = δz ^ 4 * u2 := by decide +kernel

theorem isOdd_u2 : IsOdd u2 := by decide +kernel

/-! ### Divisibility by powers of `δ` -/

theorem δz_sq_eq : δz ^ 2 = ⟨1, 2, 1, 0⟩ := by decide +kernel

theorem δz_cube_eq : δz ^ 3 = ⟨1, 3, 3, 1⟩ := by decide +kernel

theorem δz_sq_dvd_iff (x : ZOmega) :
    δz ^ 2 ∣ x ↔ (x.a + x.b + x.c + x.d) % 2 = 0 ∧ (x.b + x.d) % 2 = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [δz_sq_eq]
    simp only [a_mul, b_mul, c_mul, d_mul]
    omega
  · rintro ⟨h0, h1⟩
    refine ⟨divδ (divδ x), ?_⟩
    have e1 : ¬ IsOdd x := by simp only [IsOdd]; omega
    have e2 : ¬ IsOdd (divδ x) := by simp only [IsOdd, divδ]; omega
    rw [pow_two, mul_assoc, δz_mul_divδ e2, δz_mul_divδ e1]

theorem δz_pow_three_dvd_iff (x : ZOmega) :
    δz ^ 3 ∣ x ↔ (x.a + x.b + x.c + x.d) % 2 = 0 ∧ (x.b + x.d) % 2 = 0 ∧ (x.c + x.d) % 2 = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [δz_cube_eq]
    simp only [a_mul, b_mul, c_mul, d_mul]
    omega
  · rintro ⟨h0, h1, h2⟩
    exact δz_pow_three_dvd h0 h1 h2

/-- `δ³ ∣ 2 y`. -/
theorem δz_pow_three_dvd_two_mul (y : ZOmega) : δz ^ 3 ∣ (1 + 1) * y :=
  ⟨δz * u2 * y, by rw [two_eq_δz_pow_four]; ring⟩

/-! ### Residues modulo `δ³` -/

theorem isOdd_one : IsOdd 1 := by decide

theorem res_one : res 1 = 0 := by decide

/-- Odd elements congruent modulo `δ³` have the same residue. -/
theorem res_of_dvd {x y : ZOmega} (hx : IsOdd x) (h : δz ^ 3 ∣ x - y) :
    IsOdd y ∧ res y = res x := by
  rw [δz_pow_three_dvd_iff] at h
  simp only [a_sub, b_sub, c_sub, d_sub] at h
  unfold IsOdd at hx ⊢
  unfold res
  refine ⟨by omega, ?_⟩
  split_ifs <;> omega

theorem isOdd_ωz_pow (r : ℕ) : IsOdd (ωz ^ r) ∧ res (ωz ^ r) = r % 4 := by
  have := res_ωz_pow_mul isOdd_one r
  rw [mul_one, res_one, zero_add] at this
  exact this

/-- Lemma 11: an odd `x` is `≡ ω^{res x} (mod δ³)`. -/
theorem dvd_sub_ωz_pow_res {x : ZOmega} (hx : IsOdd x) : δz ^ 3 ∣ x - ωz ^ res x := by
  obtain ⟨h1, h2⟩ := isOdd_ωz_pow (res x)
  refine (δz_pow_three_dvd_add_sub hx h1 ?_).2
  rw [h2, Nat.mod_eq_of_lt (res_lt x)]

/-- The residue of Lemma 11 is multiplicative. -/
theorem res_mul {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y) :
    IsOdd (x * y) ∧ res (x * y) = (res x + res y) % 4 := by
  obtain ⟨a, ha⟩ := dvd_sub_ωz_pow_res hx
  obtain ⟨b, hb⟩ := dvd_sub_ωz_pow_res hy
  obtain ⟨h1, h2⟩ := isOdd_ωz_pow (res x + res y)
  have hd : δz ^ 3 ∣ ωz ^ (res x + res y) - x * y :=
    ⟨-(a * y + ωz ^ res x * b), by
      rw [pow_add]
      linear_combination (-y) * ha - ωz ^ res x * hb⟩
  obtain ⟨h3, h4⟩ := res_of_dvd h1 hd
  exact ⟨h3, h4.trans h2⟩

/-- A unit factor does not change the exponent of a syllable. -/
theorem zexp_mul_left {c x y : ZOmega} (hc : IsOdd c) (hx : IsOdd x) (hy : IsOdd y) :
    zexp (c * x) (c * y) = zexp x y := by
  have h1 := (res_mul hc hx).2
  have h2 := (res_mul hc hy).2
  have := res_lt c
  have := res_lt x
  have := res_lt y
  unfold zexp
  rw [h1, h2]
  omega

theorem isOdd_mul {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y) : IsOdd (x * y) :=
  (res_mul hx hy).1

theorem isOdd_ηz : IsOdd ηz := by decide

theorem zexp_swap {x y : ZOmega} : zexp y x = (4 - zexp x y) % 4 := by
  have := res_lt x
  have := res_lt y
  unfold zexp
  omega

theorem zexp_ωz_mul {x y : ZOmega} (hx : IsOdd x) :
    zexp (ωz * x) y = (zexp x y + 3) % 4 := by
  have h := res_ωz_mul hx
  have := res_lt x
  have := res_lt y
  unfold zexp
  rw [h]
  omega

/-- Adding `δ²` times an odd element adds `2` to the residue. -/
theorem res_add_δz_sq_mul {e w : ZOmega} (he : IsOdd e) (hw : IsOdd w) :
    IsOdd (e + δz ^ 2 * w) ∧ res (e + δz ^ 2 * w) = (res e + 2) % 4 := by
  have h1 : IsOdd (e + δz ^ 2) ∧ res (e + δz ^ 2) = (res e + 2) % 4 := by
    rw [δz_sq_eq]
    unfold IsOdd at he ⊢
    unfold res
    simp only [a_add, b_add, c_add, d_add]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega
  have hd : δz ^ 3 ∣ (e + δz ^ 2) - (e + δz ^ 2 * w) := by
    obtain ⟨q, hq⟩ := (dvd_δz_iff (1 - w)).2 (by
      unfold IsOdd at hw ⊢
      simp only [a_sub, b_sub, c_sub, d_sub, a_one, b_one, c_one, d_one]
      omega)
    exact ⟨q, by linear_combination δz ^ 2 * hq⟩
  obtain ⟨h2, h3⟩ := res_of_dvd h1.1 hd
  exact ⟨h2, h3.trans h1.2⟩

/-! ### Two entries under `H` -/

theorem s0_divδ (w : ZOmega) :
    ((divδ w).a + (divδ w).b + (divδ w).c + (divδ w).d) % 2 = (w.b + w.d) % 2 := by
  simp only [divδ]
  omega

theorem s2_δz_sq_mul (e : ZOmega) :
    ((δz ^ 2 * e).c + (δz ^ 2 * e).d) % 2 = (e.a + e.b + e.c + e.d) % 2 := by
  rw [δz_sq_eq]; simp only [c_mul, d_mul]; omega

theorem res_bit1 (x : ZOmega) : (x.b + x.d) % 2 = ((res x % 2 : ℕ) : ℤ) := by
  unfold res; split_ifs <;> omega

theorem res_bit2 (x : ZOmega) : (x.c + x.d) % 2 = ((res x / 2 : ℕ) : ℤ) := by
  have := res_lt x
  unfold res at this ⊢; split_ifs <;> omega

/-- `(x + y) - (x - y) = 2 y`. -/
theorem add_sub_sub_eq (x y : ZOmega) : (x + y) - (x - y) = (1 + 1) * y := by ring

/-- Two odd entries whose residues differ by an odd number: `x ± y = δ e±`
with `e±` odd of the same residue (Subcases 1.2 and 1.3). -/
theorem pair_oo_odd {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y)
    (hz : (res x + res y) % 2 = 1) :
    ∃ e1 e2, x + y = δz * e1 ∧ x - y = δz * e2 ∧ IsOdd e1 ∧ IsOdd e2 ∧ res e1 = res e2 := by
  have hpx := res_bit1 x
  have hpy := res_bit1 y
  have hs : ¬ IsOdd (x + y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_add, b_add, c_add, d_add]; omega
  have hd : ¬ IsOdd (x - y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_sub, b_sub, c_sub, d_sub]; omega
  have e1 := δz_mul_divδ hs
  have e2 := δz_mul_divδ hd
  have o1 : IsOdd (divδ (x + y)) := by
    unfold IsOdd; rw [s0_divδ]; simp only [b_add, d_add]; omega
  have o2 : IsOdd (divδ (x - y)) := by
    unfold IsOdd; rw [s0_divδ]; simp only [b_sub, d_sub]; omega
  refine ⟨divδ (x + y), divδ (x - y), e1.symm, e2.symm, o1, o2, ?_⟩
  have hdiff : divδ (x + y) - divδ (x - y) = δz ^ 3 * (u2 * y) := by
    apply δz_mul_cancel
    rw [mul_sub, e1, e2, add_sub_sub_eq, two_eq_δz_pow_four]
    ring
  exact (res_of_dvd o1 ⟨u2 * y, hdiff⟩).2.symm

/-- Two odd entries with residues differing by `2`: `x ± y = δ² e±` with
`e±` odd and `zexp e+ e- = 2` (Subcase 1.4). -/
theorem pair_oo_two {x y : ZOmega} (hx : IsOdd x) (hy : IsOdd y) (hz : zexp x y = 2) :
    ∃ e1 e2, x + y = δz ^ 2 * e1 ∧ x - y = δz ^ 2 * e2 ∧ IsOdd e1 ∧ IsOdd e2 ∧
      zexp e1 e2 = 2 := by
  have h1x := res_bit1 x
  have h1y := res_bit1 y
  have h2x := res_bit2 x
  have h2y := res_bit2 y
  have hrx := res_lt x
  have hry := res_lt y
  unfold zexp at hz
  obtain ⟨e1, he1⟩ := (δz_sq_dvd_iff (x + y)).2 (by
    unfold IsOdd at hx hy; simp only [a_add, b_add, c_add, d_add]; omega)
  obtain ⟨e2, he2⟩ := (δz_sq_dvd_iff (x - y)).2 (by
    unfold IsOdd at hx hy; simp only [a_sub, b_sub, c_sub, d_sub]; omega)
  have o1 : IsOdd e1 := by
    have := s2_δz_sq_mul e1
    rw [← he1] at this; simp only [c_add, d_add] at this
    unfold IsOdd; omega
  have o2 : IsOdd e2 := by
    have := s2_δz_sq_mul e2
    rw [← he2] at this; simp only [c_sub, d_sub] at this
    unfold IsOdd; omega
  have hdiff : e1 = e2 + δz ^ 2 * (u2 * y) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 δz_ne_zero)
    have h := add_sub_sub_eq x y
    rw [he1, he2, two_eq_δz_pow_four] at h
    linear_combination h
  obtain ⟨-, h3⟩ := res_add_δz_sq_mul o2 (isOdd_mul isOdd_u2 hy)
  refine ⟨e1, e2, he1, he2, o1, o2, ?_⟩
  have := res_lt e2
  unfold zexp
  rw [hdiff, h3]
  omega

/-- One odd and one even entry: `x ± y` are odd with the same residue
(Subcase 1.5). -/
theorem pair_oe {x y : ZOmega} (hx : IsOdd x) (hy : ¬ IsOdd y) :
    IsOdd (x + y) ∧ IsOdd (x - y) ∧ res (x + y) = res (x - y) := by
  have o1 : IsOdd (x + y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_add, b_add, c_add, d_add]; omega
  have h := res_of_dvd o1 (by rw [add_sub_sub_eq]; exact δz_pow_three_dvd_two_mul y)
  exact ⟨o1, h.1, h.2.symm⟩

/-- One even and one odd entry: `x ± y` are odd with the same residue. -/
theorem pair_eo {x y : ZOmega} (hx : ¬ IsOdd x) (hy : IsOdd y) :
    IsOdd (x + y) ∧ IsOdd (x - y) ∧ res (x + y) = res (x - y) := by
  have o1 : IsOdd (x + y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_add, b_add, c_add, d_add]; omega
  have h := res_of_dvd o1 (by rw [add_sub_sub_eq]; exact δz_pow_three_dvd_two_mul y)
  exact ⟨o1, h.1, h.2.symm⟩

/-- Two even entries (Subcases 1.6.1–1.6.3): `x ± y` are both divisible by
`δ³`, or `x ± y = δ² e±`, or `x ± y = δ e±`, with `e±` odd of the same
residue. -/
theorem pair_ee {x y : ZOmega} (hx : ¬ IsOdd x) (hy : ¬ IsOdd y) :
    (δz ^ 3 ∣ x + y ∧ δz ^ 3 ∣ x - y) ∨
    (∃ e1 e2, x + y = δz ^ 2 * e1 ∧ x - y = δz ^ 2 * e2 ∧ IsOdd e1 ∧ IsOdd e2 ∧
      res e1 = res e2) ∨
    (∃ e1 e2, x + y = δz * e1 ∧ x - y = δz * e2 ∧ IsOdd e1 ∧ IsOdd e2 ∧ res e1 = res e2) := by
  obtain ⟨y', hy'⟩ := (dvd_δz_iff y).2 hy
  have hs : ¬ IsOdd (x + y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_add, b_add, c_add, d_add]; omega
  have hd : ¬ IsOdd (x - y) := by
    unfold IsOdd at hx hy ⊢; simp only [a_sub, b_sub, c_sub, d_sub]; omega
  by_cases h1 : ((x + y).b + (x + y).d) % 2 = 1
  · -- `δ` exactly
    right; right
    have e1 := δz_mul_divδ hs
    have e2 := δz_mul_divδ hd
    have o1 : IsOdd (divδ (x + y)) := by unfold IsOdd; rw [s0_divδ]; omega
    have o2 : IsOdd (divδ (x - y)) := by
      unfold IsOdd; rw [s0_divδ]
      unfold IsOdd at hy; simp only [b_add, d_add] at h1; simp only [b_sub, d_sub]; omega
    refine ⟨divδ (x + y), divδ (x - y), e1.symm, e2.symm, o1, o2, ?_⟩
    have hdiff : divδ (x + y) - divδ (x - y) = δz ^ 3 * (u2 * y) := by
      apply δz_mul_cancel
      rw [mul_sub, e1, e2, add_sub_sub_eq, two_eq_δz_pow_four]
      ring
    exact (res_of_dvd o1 ⟨u2 * y, hdiff⟩).2.symm
  by_cases h2 : ((x + y).c + (x + y).d) % 2 = 1
  · -- `δ²` exactly
    right; left
    simp only [b_add, d_add, c_add] at h1 h2
    unfold IsOdd at hx hy
    obtain ⟨e1, he1⟩ := (δz_sq_dvd_iff (x + y)).2 (by
      simp only [a_add, b_add, c_add, d_add]; omega)
    obtain ⟨e2, he2⟩ := (δz_sq_dvd_iff (x - y)).2 (by
      simp only [a_sub, b_sub, c_sub, d_sub]; omega)
    have o1 : IsOdd e1 := by
      have := s2_δz_sq_mul e1
      rw [← he1] at this; simp only [c_add, d_add] at this
      unfold IsOdd; omega
    have o2 : IsOdd e2 := by
      have := s2_δz_sq_mul e2
      rw [← he2] at this; simp only [c_sub, d_sub] at this
      unfold IsOdd; omega
    have hdiff : e1 - e2 = δz ^ 3 * (u2 * y') := by
      apply mul_left_cancel₀ (pow_ne_zero 2 δz_ne_zero)
      have h := add_sub_sub_eq x y
      rw [he1, he2, two_eq_δz_pow_four, hy'] at h
      linear_combination h
    exact ⟨e1, e2, he1, he2, o1, o2, (res_of_dvd o1 ⟨u2 * y', hdiff⟩).2.symm⟩
  · -- `δ³`
    left
    simp only [b_add, d_add, c_add] at h1 h2
    unfold IsOdd at hx hy
    constructor
    · exact δz_pow_three_dvd (by simp only [a_add, b_add, c_add, d_add]; omega)
        (by simp only [b_add, d_add]; omega) (by simp only [c_add, d_add]; omega)
    · exact δz_pow_three_dvd (by simp only [a_sub, b_sub, c_sub, d_sub]; omega)
        (by simp only [b_sub, d_sub]; omega) (by simp only [c_sub, d_sub]; omega)

end ZOmega

end QCert.Greylyn
