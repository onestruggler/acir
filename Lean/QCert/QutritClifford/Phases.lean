/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Scalars and phases of the qutrit Clifford group

* Proposition 2.8: an operator that fixes every Pauli by conjugation is a
  scalar (`scalar_of_fixes`).  The paper argues that the Paulis span all
  matrices; here the `Z`-type Paulis force the operator to be diagonal and
  the `X`-type Paulis make the diagonal constant.
* Lemma B.1 and Proposition B.2: the elements of `ℤ[1/3, ω]` of norm one are
  the six powers of `-ω` (`phase_of_mem`).
* Corollary B.3: two Clifford operators that act alike on the Paulis differ
  by a power of `-ω` (`same_action_phase`).
-/
import QCert.QutritClifford.Pauli
import Mathlib.Tactic.IntervalCases

namespace QCert.QutritClifford

open Matrix

noncomputable section

/-! ### The cube roots of unity -/

theorem ωℂ_sum : ωℂ ^ 2 + ωℂ + 1 = 0 := by
  rw [ωℂ_eq]; linear_combination ζ_pow_four

theorem ωℂ_ne_one : ωℂ ≠ 1 := by
  intro h
  have := ωℂ_sum
  rw [h] at this
  norm_num at this

theorem ωℂ_sq_ne_one : ωℂ ^ 2 ≠ 1 := by
  intro h
  exact ωℂ_ne_one (by linear_combination -ωℂ * h + ωℂ_pow_three)

theorem ωℂ_ne_sq : ωℂ ≠ ωℂ ^ 2 := by
  intro h
  have h3 : (3 : ℂ) = 0 := by linear_combination (-(2 * ωℂ + 1)) * h + (3 - 2 * ωℂ) * ωℂ_sum
  norm_num at h3

/-- `x ↦ ωˣ` is injective on `ℤ/3`. -/
theorem ωℂ_pow_inj (x y : Fin 3) (h : ωℂ ^ (x : ℕ) = ωℂ ^ (y : ℕ)) : x = y := by
  have h1 := ωℂ_ne_one
  have h1' := Ne.symm ωℂ_ne_one
  have h2 := ωℂ_sq_ne_one
  have h2' := Ne.symm ωℂ_sq_ne_one
  have h3 := ωℂ_ne_sq
  have h3' := Ne.symm ωℂ_ne_sq
  fin_cases x <;> fin_cases y <;> simp_all

/-! ### Proposition 2.8 -/

/-- `Z^(j)`: `Z` on wire `j`, a diagonal operator. -/
theorem pauliZ_single {n : ℕ} (j : Fin n) :
    pauli 0 0 (Pi.single j 1) = diagonal fun t : State 3 n => ωℂ ^ (t j : ℕ) := by
  ext s t
  rw [pauli_apply, diagonal_apply]
  have hs : (s = fun i => t i + (0 : Fin n → Fin 3) i) ↔ s = t := by
    constructor <;> intro h <;> funext i <;> simp [h]
  have hp : ∏ i, ωℂ ^ (((Pi.single j 1 : Fin n → Fin 3) i : ℕ) * (t i : ℕ)) =
      ωℂ ^ (t j : ℕ) := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  by_cases h : s = t
  · subst h; rw [if_pos (hs.2 rfl), if_pos rfl, hp]; simp
  · rw [if_neg (fun h' => h (hs.1 h')), if_neg h]

/-- `X`-type Paulis are permutations: `|t⟩ ↦ |t + a⟩`. -/
theorem pauliX_apply {n : ℕ} (a s t : State 3 n) :
    pauli 0 a 0 s t = if s = t + a then 1 else 0 := by
  rw [pauli_apply]
  have hs : (s = fun i => t i + a i) ↔ s = t + a := Iff.rfl
  by_cases h : s = t + a
  · rw [if_pos (hs.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (hs.1 h')), if_neg h]

/-- **Proposition 2.8**: a unitary that fixes every Pauli by conjugation is a
scalar. -/
theorem scalar_of_fixes {n : ℕ} {U : Op ℂ 3 n} (hU : star U * U = 1)
    (h : ∀ P ∈ pauliGroup n, U * P * star U = P) : U = U 0 0 • (1 : Op ℂ 3 n) := by
  have comm : ∀ P ∈ pauliGroup n, U * P = P * U := by
    intro P hP
    calc U * P = U * P * (star U * U) := by rw [hU, mul_one]
      _ = U * P * star U * U := by simp only [mul_assoc]
      _ = P * U := by rw [h P hP]
  have hdiag : ∀ s t, s ≠ t → U s t = 0 := by
    intro s t hst
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ t j := by
      by_contra hc
      exact hst (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
    have e := congrFun (congrFun (comm _ ⟨⟨0, 0, Pi.single j 1⟩, rfl⟩) s) t
    simp only [pauliZ_single, mul_diagonal, diagonal_mul] at e
    have hne : ωℂ ^ (t j : ℕ) - ωℂ ^ (s j : ℕ) ≠ 0 :=
      sub_ne_zero.2 fun e' => hj (ωℂ_pow_inj _ _ e').symm
    have e2 : (ωℂ ^ (t j : ℕ) - ωℂ ^ (s j : ℕ)) * U s t = 0 := by linear_combination e
    exact (mul_eq_zero.1 e2).resolve_left hne
  have hU' : U = diagonal fun s => U s s := by
    ext s t
    rw [diagonal_apply]
    split_ifs with hst
    · rw [hst]
    · exact hdiag s t hst
  have hconst : ∀ s, U s s = U 0 0 := by
    intro s
    have e := congrFun (congrFun (comm _ ⟨⟨0, s, 0⟩, rfl⟩) s) 0
    rw [hU'] at e
    simp only [diagonal_mul, mul_diagonal, pauliX_apply, zero_add, if_true, mul_one,
      one_mul] at e
    exact e
  ext s t
  rw [smul_apply, one_apply, smul_eq_mul]
  split_ifs with hst
  · rw [hst, hconst, mul_one]
  · rw [hdiag s t hst, mul_zero]

/-! ### Lemma B.1 and Proposition B.2 -/

/-- The elements of `ℤ[1/3, ω]` are the `(a + b ω)/3^k`. -/
theorem mem_ZThirdOmega {x : ℂ} (hx : x ∈ ZThirdOmega) :
    ∃ a b : ℤ, ∃ k : ℕ, x * 3 ^ k = a + b * ωℂ := by
  unfold ZThirdOmega at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, 1, by norm_num⟩
    · exact ⟨0, 1, 0, by simp⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | one => exact ⟨1, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, k, hk⟩ := hx
    obtain ⟨c, d, l, hl⟩ := hy
    refine ⟨a * 3 ^ l + c * 3 ^ k, b * 3 ^ l + d * 3 ^ k, k + l, ?_⟩
    push_cast
    linear_combination (3 : ℂ) ^ l * hk + (3 : ℂ) ^ k * hl
  | neg x _ hx =>
    obtain ⟨a, b, k, hk⟩ := hx
    exact ⟨-a, -b, k, by push_cast; linear_combination -hk⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, k, hk⟩ := hx
    obtain ⟨c, d, l, hl⟩ := hy
    refine ⟨a * c - b * d, a * d + b * c - b * d, k + l, ?_⟩
    push_cast
    linear_combination (y * 3 ^ l) * hk + (a + b * ωℂ) * hl + b * d * ωℂ_sum

/-- `ℤ[1/3, ω]` is closed under complex conjugation. -/
theorem star_mem_ZThirdOmega {x : ℂ} (hx : x ∈ ZThirdOmega) : star x ∈ ZThirdOmega := by
  unfold ZThirdOmega at hx ⊢
  induction hx using Subring.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [show star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ by simp]
      exact Subring.subset_closure (by simp)
    · rw [star_ωℂ]
      exact Subring.pow_mem _ (Subring.subset_closure (by simp)) 2
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [star_add]; exact Subring.add_mem _ hx hy
  | neg x _ hx => rw [star_neg]; exact Subring.neg_mem _ hx
  | mul x y _ _ hx hy => rw [star_mul']; exact Subring.mul_mem _ hx hy

/-- **Lemma B.1**, in the form the proof of Proposition B.2 uses: if
`a² - ab + b² ≡ 0 (mod 9)` then `a ≡ b ≡ 0 (mod 3)`. -/
theorem three_dvd_of_nine_dvd {a b : ℤ} (h : (9 : ℤ) ∣ a ^ 2 - a * b + b ^ 2) :
    3 ∣ a ∧ 3 ∣ b := by
  have key : ∀ x y : ZMod 9, x ^ 2 - x * y + y ^ 2 = 0 → 3 * x = 0 ∧ 3 * y = 0 := by decide
  have h9 : ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).2 h
  push_cast at h9
  obtain ⟨ha, hb⟩ := key _ _ h9
  have conv : ∀ z : ℤ, 3 * (z : ZMod 9) = 0 → 3 ∣ z := by
    intro z hz
    have : ((3 * z : ℤ) : ZMod 9) = 0 := by push_cast; exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    omega
  exact ⟨conv a ha, conv b hb⟩

/-- `a² - ab + b² = 9ᵏ` forces `a`, `b` to be `3ᵏ` times a solution of
`a² - ab + b² = 1`. -/
theorem norm_eq_pow_nine : ∀ (k : ℕ) (a b : ℤ), a ^ 2 - a * b + b ^ 2 = 9 ^ k →
    ∃ a' b' : ℤ, a = 3 ^ k * a' ∧ b = 3 ^ k * b' ∧ a' ^ 2 - a' * b' + b' ^ 2 = 1
  | 0, a, b, h => ⟨a, b, by simp, by simp, by simpa using h⟩
  | k + 1, a, b, h => by
    obtain ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩ := three_dvd_of_nine_dvd (a := a) (b := b)
      ⟨9 ^ k, by rw [h, pow_succ']⟩
    have h' : c ^ 2 - c * d + d ^ 2 = 9 ^ k := by
      have e : 9 * (c ^ 2 - c * d + d ^ 2) = 9 * 9 ^ k := by
        rw [← pow_succ']; linear_combination h
      exact mul_left_cancel₀ (by norm_num) e
    obtain ⟨a', b', ha, hb, h1⟩ := norm_eq_pow_nine k c d h'
    exact ⟨a', b', by rw [ha]; ring, by rw [hb]; ring, h1⟩

/-- The six solutions of `a² - ab + b² = 1`. -/
theorem norm_one {a b : ℤ} (h : a ^ 2 - a * b + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) ∨
      (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (2 * a - b)]
  have hb0 : -1 ≤ b := by nlinarith [sq_nonneg (2 * a - b)]
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (2 * b - a)]
  have ha0 : -1 ≤ a := by nlinarith [sq_nonneg (2 * b - a)]
  interval_cases a <;> interval_cases b <;> simp_all

/-- **Proposition B.2**: an element of `ℤ[1/3, ω]` of norm one is one of the
six powers of `-ω`. -/
theorem phase_of_mem {x : ℂ} (hx : x ∈ ZThirdOmega) (h1 : star x * x = 1) :
    ∃ t : ℕ, t < 6 ∧ x = (-ωℂ) ^ t := by
  obtain ⟨a, b, k, hk⟩ := mem_ZThirdOmega hx
  have hs : star x * 3 ^ k = a + b * ωℂ ^ 2 := by
    have e : star (x * 3 ^ k) = star ((a : ℂ) + b * ωℂ) := by rw [hk]
    rw [star_mul', star_add, star_mul', star_pow, star_ωℂ] at e
    simpa using e
  have h93 : (3 : ℂ) ^ k * 3 ^ k = 9 ^ k := by rw [← mul_pow]; norm_num
  have hC : (a : ℂ) ^ 2 - a * b + b ^ 2 = 9 ^ k := by
    linear_combination (-(x * 3 ^ k)) * hs - (a + b * ωℂ ^ 2) * hk + (3 ^ k * 3 ^ k) * h1 -
      (a * b) * ωℂ_sum - b ^ 2 * ωℂ_pow_three + h93
  have hz : a ^ 2 - a * b + b ^ 2 = 9 ^ k := by exact_mod_cast hC
  obtain ⟨a', b', rfl, rfl, h1'⟩ := norm_eq_pow_nine k a b hz
  have hx' : x = a' + b' * ωℂ := by
    have h3 : (3 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_right_cancel₀ h3
    rw [hk]; push_cast; ring
  rcases norm_one h1' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  · exact ⟨0, by norm_num, by rw [hx']; push_cast; ring⟩
  · exact ⟨3, by norm_num, by rw [hx']; push_cast; linear_combination ωℂ_pow_three⟩
  · exact ⟨4, by norm_num, by rw [hx']; push_cast; linear_combination (-ωℂ) * ωℂ_pow_three⟩
  · exact ⟨1, by norm_num, by rw [hx']; push_cast; ring⟩
  · exact ⟨5, by norm_num, by
      rw [hx']; push_cast; linear_combination ωℂ_sum + ωℂ ^ 2 * ωℂ_pow_three⟩
  · exact ⟨2, by norm_num, by rw [hx']; push_cast; linear_combination -ωℂ_sum⟩

/-! ### Corollary B.3 -/

/-- **Corollary B.3**: two Clifford operators that act alike on the Paulis
differ by a power of `-ω`. -/
theorem same_action_phase {n : ℕ} (U V : cliffordGroup n)
    (h : ∀ P ∈ pauliGroup n, ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) * P *
      star ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) =
      ((V : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) * P *
      star ((V : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n)) :
    ∃ t : ℕ, t < 6 ∧ ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) =
      (-ωℂ) ^ t • ((V : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) := by
  obtain ⟨hu, hu'⟩ := Unitary.mem_iff.1 (U : unitaryGroup (State 3 n) ℂ).2
  obtain ⟨hv, hv'⟩ := Unitary.mem_iff.1 (V : unitaryGroup (State 3 n) ℂ).2
  set u : Op ℂ 3 n := ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) with hu_def
  set v : Op ℂ 3 n := ((V : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) with hv_def
  have hW : star (star v * u) * (star v * u) = 1 := by
    rw [star_mul, star_star]
    calc star u * v * (star v * u) = star u * (v * star v) * u := by simp only [mul_assoc]
      _ = 1 := by rw [hv', mul_one, hu]
  have hfix : ∀ P ∈ pauliGroup n, star v * u * P * star (star v * u) = P := by
    intro P hP
    rw [star_mul, star_star]
    calc star v * u * P * (star u * v) = star v * (u * P * star u) * v := by
          simp only [mul_assoc]
      _ = star v * (v * P * star v) * v := by rw [h P hP]
      _ = (star v * v) * P * (star v * v) := by simp only [mul_assoc]
      _ = P := by rw [hv, one_mul, mul_one]
  have hscal := scalar_of_fixes hW hfix
  have hmem : (star v * u) 0 0 ∈ ZThirdOmega := by
    rw [mul_apply]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _
      (by rw [star_apply]; exact star_mem_ZThirdOmega (V.2.1 i 0)) (U.2.1 i 0)
  have hnorm : star ((star v * u) 0 0) * (star v * u) 0 0 = 1 := by
    have e := congrFun (congrFun hW 0) 0
    rw [hscal] at e
    simpa [smul_apply, one_apply, star_smul, mul_comm] using e
  obtain ⟨t, ht, hc⟩ := phase_of_mem hmem hnorm
  refine ⟨t, ht, ?_⟩
  calc u = v * (star v * u) := by rw [← mul_assoc, hv', one_mul]
    _ = v * ((star v * u) 0 0 • (1 : Op ℂ 3 n)) := by rw [← hscal]
    _ = (-ωℂ) ^ t • v := by rw [mul_smul_comm, mul_one, hc]

end

end QCert.QutritClifford
