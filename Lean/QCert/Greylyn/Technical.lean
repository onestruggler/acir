/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the technical lemmas of §3.3.6

The facts behind Subcase 4.3.3 of the proof of Lemma 31, in coordinates.

* Lemma 35 (`√2 ∣ x + x†`) and Lemma 36 (`x ≡ y (mod δ²)` gives
  `x† x ≡ y† y (mod 2)`) are used here in the form: modulo `2`, the integer
  part of `x† x` is `a + b + c + d` and its `√2`-part is `(a + c)(b + d)`,
  and both depend only on the class of `x` modulo `δ²`, which is given by
  the parities of `a + b + c + d` and `b + d` (`δz_sq_dvd_iff`).
* Lemma 37: four elements in the four classes `0, 1, δ, 1 + δ` modulo `δ²`
  have `Σ x† x ≡ √2 (mod 2)`: one of them is in the class `δ`, which alone
  has an odd `√2`-part (`nrm1_bits`).
* Lemma 38: a unit vector has least δ-exponent `≠ 1`.  The thesis cites
  Ross–Selinger; here it is proved directly: at `k = 1`,
  `Σ x† x = δ† δ = 2 + √2`, so the integer parts `a² + b² + c² + d²` add up
  to `2`; the odd entries, of which there are at least two, are then two
  units, whose `√2`-parts vanish, against the `√2` of `2 + √2`.
* Lemma 39: no unit vector in dimension `4` has a numerator whose entries
  lie in the four classes modulo `δ²` (`no_four_classes`): at `k = 0` the
  integer part `1` is odd, `k = 1` is Lemma 38, and for `k ≥ 2`
  `(2 + √2)ᵏ ≡ 0 (mod 2)`.
-/
import QCert.Greylyn.Exponent
import QCert.Greylyn.Residue

namespace QCert.Greylyn

open Complex ZOmega

noncomputable section

namespace ZOmega

/-- The `√2`-coordinate, as an additive map. -/
def bHom : ZOmega →+ ℤ where
  toFun := ZOmega.b
  map_zero' := rfl
  map_add' _ _ := rfl

theorem b_sum {ι : Type*} (s : Finset ι) (f : ι → ZOmega) :
    (∑ i ∈ s, f i).b = ∑ i ∈ s, (f i).b :=
  map_sum bHom f s

theorem Dz_sq : Dz ^ 2 = ⟨6, 4, 0, -4⟩ := by decide +kernel

/-- `(2 + √2)ᵏ`: `1` for `k = 0`, `2 + √2` for `k = 1`, and `≡ 0 (mod 2)` for
`k ≥ 2`. -/
theorem Dz_pow_parity (K : ℕ) : (K = 0 → (Dz ^ K).a = 1) ∧
    (K = 1 → (Dz ^ K).a = 2 ∧ (Dz ^ K).b = 1) ∧
    (2 ≤ K → (Dz ^ K).a % 2 = 0 ∧ (Dz ^ K).b % 2 = 0) := by
  refine ⟨fun h => by subst h; decide, fun h => by subst h; decide, fun h => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 2 := ⟨K - 2, by omega⟩
  obtain ⟨p, q, hpq, -⟩ := Dz_pow j
  rw [pow_add, hpq, Dz_sq]
  simp only [a_mul, b_mul]
  omega

theorem nrm1_eq (x : ZOmega) : nrm1 x = (x.a + x.c) * (x.b + x.d) - 2 * (x.a * x.d) := by
  unfold nrm1; ring

theorem nrm1_emod_two (x : ZOmega) :
    nrm1 x % 2 = ((x.a + x.c) % 2) * ((x.b + x.d) % 2) := by
  rw [nrm1_eq]
  have h1 : ((x.a + x.c) * (x.b + x.d) - 2 * (x.a * x.d)) % 2 =
      ((x.a + x.c) * (x.b + x.d)) % 2 := by omega
  rw [h1, Int.mul_emod]
  rcases Int.emod_two_eq_zero_or_one (x.a + x.c) with h | h <;>
    rcases Int.emod_two_eq_zero_or_one (x.b + x.d) with h' | h' <;> simp [h, h']

/-- A unit `ωᵐ` has no `√2`-part in `x† x`. -/
theorem nrm1_of_nrm0_eq_one {x : ZOmega} (h : nrm0 x = 1) : nrm1 x = 0 := by
  rw [← ωz_pow_uexp h]
  have h1 := one_le_uexp x
  have h2 := uexp_le x
  generalize uexp x = m at h1 h2
  interval_cases m <;> decide +kernel

theorem sq_class_iff (x y : ZOmega) :
    δz ^ 2 ∣ x - y ↔ (x.a + x.b + x.c + x.d) % 2 = (y.a + y.b + y.c + y.d) % 2 ∧
      (x.b + x.d) % 2 = (y.b + y.d) % 2 := by
  rw [δz_sq_dvd_iff]
  simp only [a_sub, b_sub, c_sub, d_sub]
  omega

end ZOmega

variable {n : ℕ}

/-- For a unit vector, `Σ (√2-part of wⱼ† wⱼ)` is the `√2`-part of
`(2 + √2)ᵏ`. -/
theorem sum_nrm1_eq {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → ZOmega} (h : HasNum v k w) : ∑ j, nrm1 (w j) = (Dz ^ k).b := by
  rw [← sum_cj_mul_eq hv h, b_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [cj_mul_self]

/-- Lemma 38: a unit vector does not have least δ-exponent `1`. -/
theorem lde_ne_one {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {w : Fin n → ZOmega}
    (h : HasNum v 1 w) (hodd : ∃ j, IsOdd (w j)) : False := by
  have h0 := sum_nrm0_eq hv h
  have h1 := sum_nrm1_eq hv h
  rw [((Dz_pow_parity 1).2.1 rfl).1] at h0
  rw [((Dz_pow_parity 1).2.1 rfl).2] at h1
  have hle : ∀ j, nrm0 (w j) ≤ 2 := fun j =>
    calc nrm0 (w j) ≤ ∑ i, nrm0 (w i) :=
          Finset.single_le_sum (fun i _ => nrm0_nonneg (w i)) (Finset.mem_univ j)
      _ = 2 := h0
  by_cases hbig : ∃ j, nrm0 (w j) = 2
  · -- one entry carries all of `2`; it is even, and the others vanish
    obtain ⟨j, hj⟩ := hbig
    have hrest : ∀ i, i ≠ j → nrm0 (w i) = 0 := by
      intro i hi
      have hs := Finset.add_sum_erase Finset.univ (fun i => nrm0 (w i)) (Finset.mem_univ j)
      have h2 : ∑ i ∈ Finset.univ.erase j, nrm0 (w i) = 0 := by
        simp only at hs; rw [h0, hj] at hs; linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => nrm0_nonneg (w i))).1 h2 i
        (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
    obtain ⟨j0, hj0⟩ := hodd
    by_cases hjj : j0 = j
    · subst hjj
      have := nrm0_emod_two (w j0)
      unfold IsOdd at hj0
      omega
    · rw [eq_zero_of_nrm0 (hrest j0 hjj)] at hj0
      exact not_isOdd_zero hj0
  · -- every entry is `0` or a unit, with no `√2`-part
    push Not at hbig
    have hall : ∀ j, nrm1 (w j) = 0 := by
      intro j
      have := hle j
      have := nrm0_nonneg (w j)
      have := hbig j
      rcases (show nrm0 (w j) = 0 ∨ nrm0 (w j) = 1 by omega) with h' | h'
      · rw [eq_zero_of_nrm0 h']; decide
      · exact nrm1_of_nrm0_eq_one h'
    simp [hall] at h1

theorem nrm1_bits (x : ZOmega) :
    nrm1 x % 2 ≤ (x.b + x.d) % 2 ∧ nrm1 x % 2 + (x.a + x.b + x.c + x.d) % 2 ≤ 1 ∧
      (x.b + x.d) % 2 ≤ nrm1 x % 2 + (x.a + x.b + x.c + x.d) % 2 := by
  rw [nrm1_emod_two]
  rcases Int.emod_two_eq_zero_or_one (x.a + x.c) with h | h <;>
    rcases Int.emod_two_eq_zero_or_one (x.b + x.d) with h' | h' <;>
    · rw [h, h']; omega

/-- The class bits of an element: the parities of `a + b + c + d` and `b + d`,
and of the `√2`-part of `x† x`, which is odd exactly in the class `δ`. -/
theorem bits (x : ZOmega) :
    0 ≤ (x.a + x.b + x.c + x.d) % 2 ∧ (x.a + x.b + x.c + x.d) % 2 ≤ 1 ∧
    0 ≤ (x.b + x.d) % 2 ∧ (x.b + x.d) % 2 ≤ 1 ∧ 0 ≤ nrm1 x % 2 ∧
    nrm1 x % 2 ≤ (x.b + x.d) % 2 ∧ nrm1 x % 2 + (x.a + x.b + x.c + x.d) % 2 ≤ 1 ∧
    (x.b + x.d) % 2 ≤ nrm1 x % 2 + (x.a + x.b + x.c + x.d) % 2 := by
  have := nrm1_bits x
  omega

/-- Lemma 37, the counting: four distinct classes modulo `δ²` contain
exactly one of class `δ`. -/
theorem four_bits {a0 a1 a2 a3 b0 b1 b2 b3 r0 r1 r2 r3 : ℤ}
    (h0 : 0 ≤ a0 ∧ a0 ≤ 1 ∧ 0 ≤ b0 ∧ b0 ≤ 1 ∧ 0 ≤ r0 ∧ r0 ≤ b0 ∧ r0 + a0 ≤ 1 ∧ b0 ≤ r0 + a0)
    (h1 : 0 ≤ a1 ∧ a1 ≤ 1 ∧ 0 ≤ b1 ∧ b1 ≤ 1 ∧ 0 ≤ r1 ∧ r1 ≤ b1 ∧ r1 + a1 ≤ 1 ∧ b1 ≤ r1 + a1)
    (h2 : 0 ≤ a2 ∧ a2 ≤ 1 ∧ 0 ≤ b2 ∧ b2 ≤ 1 ∧ 0 ≤ r2 ∧ r2 ≤ b2 ∧ r2 + a2 ≤ 1 ∧ b2 ≤ r2 + a2)
    (h3 : 0 ≤ a3 ∧ a3 ≤ 1 ∧ 0 ≤ b3 ∧ b3 ≤ 1 ∧ 0 ≤ r3 ∧ r3 ≤ b3 ∧ r3 + a3 ≤ 1 ∧ b3 ≤ r3 + a3)
    (d01 : ¬ (a0 = a1 ∧ b0 = b1)) (d02 : ¬ (a0 = a2 ∧ b0 = b2)) (d03 : ¬ (a0 = a3 ∧ b0 = b3))
    (d12 : ¬ (a1 = a2 ∧ b1 = b2)) (d13 : ¬ (a1 = a3 ∧ b1 = b3)) (d23 : ¬ (a2 = a3 ∧ b2 = b3)) :
    (r0 + r1 + r2 + r3) % 2 = 1 := by
  have ⟨x0, y0, z0, w0, _⟩ := h0
  have ⟨x1, y1, z1, w1, _⟩ := h1
  have ⟨x2, y2, z2, w2, _⟩ := h2
  have ⟨x3, y3, z3, w3, _⟩ := h3
  interval_cases a0 <;> interval_cases b0 <;> interval_cases a1 <;> interval_cases b1 <;>
    interval_cases a2 <;> interval_cases b2 <;> interval_cases a3 <;> interval_cases b3 <;>
    omega

/-- Lemma 39 (with Lemma 37): in dimension `4`, no unit vector has a
numerator whose entries lie in the four classes modulo `δ²` (whatever the
exponent: some entry is odd, so the exponent is the least one). -/
theorem no_four_classes {v : Fin 4 → ℂ} (hv : ∑ j, star (v j) * v j = 1) {K : ℕ}
    {y : Fin 4 → ZOmega} (h : HasNum v K y) (hd : ∀ i j, i ≠ j → ¬ δz ^ 2 ∣ y i - y j) :
    False := by
  have hc : ∀ i j, i ≠ j → ¬ (((y i).a + (y i).b + (y i).c + (y i).d) % 2 =
      ((y j).a + (y j).b + (y j).c + (y j).d) % 2 ∧
        ((y i).b + (y i).d) % 2 = ((y j).b + (y j).d) % 2) :=
    fun i j hij h' => hd i j hij ((sq_class_iff _ _).2 h')
  obtain ⟨p0, p1, p2⟩ := Dz_pow_parity K
  rcases Nat.lt_or_ge K 2 with hK | hK
  · interval_cases K
    · -- `k = 0`: Lemma 14, three entries vanish
      obtain ⟨c, -, hc0⟩ := unit_of_sum hv h
      have key : ∃ i j, i ≠ j ∧ i ≠ c ∧ j ≠ c := by
        fin_cases c
        · exact ⟨1, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
      obtain ⟨i, j, hij, hic, hjc⟩ := key
      apply hd i j hij
      rw [hc0 i hic, hc0 j hjc, sub_zero]
      exact dvd_zero _
    · -- `k = 1`: Lemma 38; some entry is odd, by pigeonhole on the classes
      have hodd : ∃ j, IsOdd (y j) := by
        by_contra hno
        push Not at hno
        have e0 := hno 0
        have e1 := hno 1
        have e2 := hno 2
        unfold IsOdd at e0 e1 e2
        have c01 := hc 0 1 (by decide)
        have c02 := hc 0 2 (by decide)
        have c12 := hc 1 2 (by decide)
        omega
      exact lde_ne_one hv h hodd
  · -- `k ≥ 2`: `(2 + √2)ᵏ ≡ 0 (mod 2)` against `√2 (mod 2)` (Lemma 37)
    have s1 := sum_nrm1_eq hv h
    rw [Fin.sum_univ_four] at s1
    have hb := (p2 hK).2
    rw [← s1] at hb
    have key := four_bits (bits (y 0)) (bits (y 1)) (bits (y 2)) (bits (y 3))
      (hc 0 1 (by decide)) (hc 0 2 (by decide)) (hc 0 3 (by decide)) (hc 1 2 (by decide))
      (hc 1 3 (by decide)) (hc 2 3 (by decide))
    omega
end

end QCert.Greylyn
