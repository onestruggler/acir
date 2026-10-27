/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: δ-exponents

Definition 9: an element `u` of `𝔻[ω] = ℤ[1/√2, i]` has a δ-exponent `k`
when `δᵏ u ∈ ℤ[ω]`; every element has one, and the least one is `lde u`.
Here for vectors: `HasNum v k w` says `δᵏ v = w` with `w` over `ℤ[ω]`, the
numerator of `v` at the exponent `k`.  For a unit vector,
`Σ wⱼ† wⱼ = (δ† δ)ᵏ = (2 + √2)ᵏ` (`sum_cj_mul_eq`), whence Lemma 14 (`k = 0`:
one nonzero entry, a power of `ω`, `unit_of_sum`) and the parity count in
the proof of Lemma 13 (`k > 0`: an even number of odd entries,
`even_card_odd`).
-/
import QCert.Greylyn.ZOmega
import QCert.Greylyn.Semantics

namespace QCert.Greylyn

open Complex ZOmega

noncomputable section

/-- `δ = 1 + ω ∈ ℂ`. -/
def δ : ℂ := 1 + QCert.ω

theorem toC_δz' : toC δz = δ := toC_δz

theorem δ_ne_zero : δ ≠ 0 := by
  rw [← toC_δz']
  intro h
  exact δz_ne_zero (eq_zero_of_toC h)

/-- `δ² / √2 = 1 + ω + ω²`. -/
theorem δ_sq_mul_invSqrt2 : δ ^ 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = toC ηz := toC_ηz

variable {n : ℕ}

/-- `δᵏ v = w`: `w` is the numerator of `v` at the δ-exponent `k`
(Definition 9). -/
def HasNum (v : Fin n → ℂ) (k : ℕ) (w : Fin n → ZOmega) : Prop :=
  ∀ j, δ ^ k * v j = toC (w j)

theorem HasNum.unique {v : Fin n → ℂ} {k : ℕ} {w w' : Fin n → ZOmega} (h : HasNum v k w)
    (h' : HasNum v k w') : w = w' := by
  funext j; exact toC_injective ((h j).symm.trans (h' j))

theorem HasNum.add_exp {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w) (d : ℕ) :
    HasNum v (k + d) (fun j => δz ^ d * w j) := by
  intro j; rw [pow_add, mul_comm (δ ^ k), mul_assoc, h j, map_mul, map_pow, toC_δz']

theorem HasNum.pred {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v (k + 1) w)
    (c : Fin n → ZOmega) (hc : ∀ j, w j = δz * c j) : HasNum v k c := by
  intro j
  have := h j
  rw [hc j, map_mul, toC_δz', pow_succ', mul_assoc] at this
  exact mul_left_cancel₀ δ_ne_zero this

theorem HasNum.pred2 {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v (k + 2) w)
    (c : Fin n → ZOmega) (hc : ∀ j, w j = δz ^ 2 * c j) : HasNum v k c := by
  have h1 : HasNum v (k + 1 + 1) w := h
  exact (h1.pred (fun j => δz * c j) fun j => by rw [hc j, pow_two, mul_assoc]).pred c
    fun _ => rfl

/-- Every element of `ℤ[1/√2, i]` has a δ-exponent (Definition 9). -/
theorem exists_num_of_mem {z : ℂ} (hz : z ∈ ZInvSqrt2I) :
    ∃ (k : ℕ) (g : ZOmega), δ ^ k * z = toC g := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨2, ηz, δ_sq_mul_invSqrt2⟩
    · exact ⟨0, iz, by rw [toC_iz, pow_zero, one_mul]⟩
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, g, hg⟩ := hx
    obtain ⟨l, g', hg'⟩ := hy
    refine ⟨k + l, δz ^ l * g + δz ^ k * g', ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, toC_δz', ← hg, ← hg']
    ring
  | neg x _ hx =>
    obtain ⟨k, g, hg⟩ := hx
    exact ⟨k, -g, by rw [map_neg, ← hg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, g, hg⟩ := hx
    obtain ⟨l, g', hg'⟩ := hy
    refine ⟨k + l, g * g', ?_⟩
    rw [map_mul, ← hg, ← hg']
    ring

/-- A vector with entries in `ℤ[1/√2, i]` has a δ-exponent. -/
theorem exists_hasNum {v : Fin n → ℂ} (hv : ∀ j, v j ∈ ZInvSqrt2I) : ∃ k w, HasNum v k w := by
  choose k g hg using fun j => exists_num_of_mem (hv j)
  let K := Finset.univ.sup k
  refine ⟨K, fun j => δz ^ (K - k j) * g j, fun j => ?_⟩
  have hle : k j ≤ K := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, toC_δz', ← hg j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

open Classical in
/-- The least δ-exponent of a vector (Definition 9). -/
def lde (v : Fin n → ℂ) : ℕ :=
  if h : ∃ k w, HasNum v k w then Nat.find h else 0

theorem lde_spec {v : Fin n → ℂ} (h : ∃ k w, HasNum v k w) : ∃ w, HasNum v (lde v) w := by
  classical
  rw [lde, dif_pos h]; exact Nat.find_spec h

theorem lde_le {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w) : lde v ≤ k := by
  classical
  have h' : ∃ k w, HasNum v k w := ⟨k, w, h⟩
  rw [lde, dif_pos h']; exact Nat.find_min' h' ⟨w, h⟩

/-- At an exponent with an odd numerator entry, the exponent is the least
one. -/
theorem lde_eq {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w)
    (hodd : k = 0 ∨ ∃ j, IsOdd (w j)) : lde v = k := by
  apply le_antisymm (lde_le h)
  rcases hodd with rfl | ⟨j, hj⟩
  · exact Nat.zero_le _
  by_contra hlt
  push Not at hlt
  obtain ⟨w', hw'⟩ := lde_spec ⟨k, w, h⟩
  obtain ⟨d, hd⟩ : ∃ d, k = lde v + (d + 1) := ⟨k - lde v - 1, by omega⟩
  subst hd
  have := (hw'.add_exp (d + 1)).unique h
  have hwj : w j = δz ^ (d + 1) * w' j := (congrFun this j).symm
  apply not_isOdd_of_dvd _ hj
  rw [hwj]
  exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) _

/-- At the least δ-exponent `k > 0`, some numerator entry is odd. -/
theorem exists_odd {v : Fin n → ℂ} {w : Fin n → ZOmega} (h : HasNum v (lde v) w)
    (hk : 0 < lde v) : ∃ j, IsOdd (w j) := by
  by_contra hno
  push Not at hno
  have hdiv : ∀ j, δz ∣ w j := fun j => (dvd_δz_iff _).2 (hno j)
  choose c hc using hdiv
  obtain ⟨k, hk'⟩ : ∃ k, lde v = k + 1 := ⟨lde v - 1, by omega⟩
  have h2 : HasNum v k c := (hk' ▸ h).pred c hc
  have := lde_le h2
  omega

/-- For a unit vector, `Σ wⱼ† wⱼ = (δ† δ)ᵏ`. -/
theorem sum_cj_mul_eq {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → ZOmega} (h : HasNum v k w) : ∑ j, cj (w j) * w j = Dz ^ k := by
  apply toC_injective
  rw [map_sum, map_pow, ← cj_δz_mul_δz, map_mul, toC_cj, toC_δz']
  have h1 : ∀ j, toC (cj (w j) * w j) = (star δ * δ) ^ k * (star (v j) * v j) := by
    intro j
    rw [map_mul, toC_cj, ← h j, star_mul', star_pow]
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, hv, mul_one]

/-- For a unit vector, `Σ (aⱼ² + bⱼ² + cⱼ² + dⱼ²)` is the integer part of
`(2 + √2)ᵏ`. -/
theorem sum_nrm0_eq {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → ZOmega} (h : HasNum v k w) : ∑ j, nrm0 (w j) = (Dz ^ k).a := by
  rw [← sum_cj_mul_eq hv h, a_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [cj_mul_self]

theorem unit_of_sum_nrm0 {w : Fin n → ZOmega} (h : ∑ j, nrm0 (w j) = 1) :
    ∃ c, nrm0 (w c) = 1 ∧ ∀ a, a ≠ c → w a = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, w c ≠ 0 := by
    by_contra hno
    push Not at hno
    simp [hno, nrm0] at h
  have hpos : 1 ≤ nrm0 (w c) := one_le_nrm0 hc
  have hrest : nrm0 (w c) + ∑ a ∈ Finset.univ.erase c, nrm0 (w a) = 1 :=
    (Finset.add_sum_erase Finset.univ (fun a => nrm0 (w a)) (Finset.mem_univ c)).trans h
  have hnn : ∀ a ∈ Finset.univ.erase c, 0 ≤ nrm0 (w a) := fun a _ => nrm0_nonneg _
  have hsum : ∑ a ∈ Finset.univ.erase c, nrm0 (w a) = 0 := by
    have := Finset.sum_nonneg hnn
    omega
  refine ⟨c, ?_, fun a ha => ?_⟩
  · have := Finset.sum_nonneg hnn
    omega
  · exact eq_zero_of_nrm0 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum a
      (Finset.mem_erase.2 ⟨ha, Finset.mem_univ a⟩))

/-- Lemma 14: a unit vector over `ℤ[ω]` (`k = 0`) has exactly one nonzero
entry, a power of `ω`. -/
theorem unit_of_sum {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1)
    {w : Fin n → ZOmega} (h : HasNum v 0 w) : ∃ c, nrm0 (w c) = 1 ∧ ∀ a, a ≠ c → w a = 0 := by
  apply unit_of_sum_nrm0
  rw [sum_nrm0_eq hv h, pow_zero]
  rfl

/-- The number of odd entries has the parity of `Σ (aⱼ² + bⱼ² + cⱼ² + dⱼ²)`. -/
theorem sum_nrm0_emod_two (w : Fin n → ZOmega) :
    (∑ j, nrm0 (w j)) % 2 = ((Finset.univ.filter fun j => IsOdd (w j)).card : ℤ) % 2 := by
  rw [Finset.sum_int_mod]
  have : ∀ j, nrm0 (w j) % 2 = if IsOdd (w j) then 1 else 0 := by
    intro j
    rw [nrm0_emod_two]
    unfold IsOdd
    split_ifs with h <;> omega
  simp_rw [this]
  rw [Finset.sum_boole]

/-- Proof of Lemma 13: at a positive exponent, a unit vector has an even
number of odd numerator entries (`u† u ≡ (δ† δ)ᵏ ≡ 0 (mod δ)`). -/
theorem even_card_odd {v : Fin n → ℂ} (hv : ∑ j, star (v j) * v j = 1) {k : ℕ}
    {w : Fin n → ZOmega} (h : HasNum v k w) (hk : 0 < k) :
    Even (Finset.univ.filter fun j => IsOdd (w j)).card := by
  have h1 := sum_nrm0_emod_two w
  rw [sum_nrm0_eq hv h] at h1
  obtain ⟨p, q, hpq, hp⟩ := Dz_pow k
  rw [hpq] at h1
  have h2 := hp hk
  simp only at h1
  rw [Nat.even_iff]
  omega

end

end QCert.Greylyn
