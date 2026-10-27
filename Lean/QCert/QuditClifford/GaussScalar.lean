/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The scalar of the multiplier is `1` (Lemma 2.15), and (C2), (C3)

The scalar `κ_a` of the circuit (T1) (`sem_M`) is
`(a/p)_L ψ(e) (λ_p √p)⁻³ p G(a⁻¹/2) ψ(e')` with the exponents `e + e' = 0`.
Since `G(b) = (b/p)_L G(1)` (the quadratic character counts the square
roots, `quadraticChar_card_sqrts`) and `((2a)⁻¹/p) = (2/p)(a/p)`, it is
`(2/p)_L λ_p⁻³ G(1)/√p`, which is `1` by Gauss's evaluation of `G(1)`
(`QCert.gauss_sum_sign`, stated in `QCert.NumberTheory.GaussSign`) and a
case analysis of `p mod 8`.  With `M_a = |x⟩ ↦ |ax⟩` exactly, (C2) is
Proposition 2.13 and (C3) is `M_g^k = M_{g^k}`.
-/
import QCert.QuditClifford.Multiplier
import QCert.NumberTheory.GaussSign
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ### Sums over `ℤ_p` -/

theorem z_bijective : Function.Bijective (z p) :=
  (Fintype.bijective_iff_injective_and_card (z p)).2 ⟨z_injective p, by simp⟩

theorem sum_z (f : ZMod p → ℂ) : ∑ n : Fin p, f (z p n) = ∑ y : ZMod p, f y :=
  Fintype.sum_bijective (z p) (z_bijective p) _ _ fun _ => rfl

theorem sum_ψZ (b : ZMod p) : ∑ y : ZMod p, ψ p (b * y) = if b = 0 then (p : ℂ) else 0 := by
  rw [← sum_z p (fun y => ψ p (b * y)), sum_ψ]

/-- The quadratic character, with values in `ℂ`. -/
def χ (a : ZMod p) : ℂ := (quadraticChar (ZMod p) a : ℂ)

theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

/-- `∑_x f(x²) = ∑_y (1 + (y/p)) f(y)`. -/
theorem sum_sq (hp2 : p ≠ 2) (f : ZMod p → ℂ) :
    ∑ x : ZMod p, f (x ^ 2) = ∑ y : ZMod p, (χ p y + 1) * f y := by
  rw [← Fintype.sum_fiberwise' (fun x : ZMod p => x ^ 2) f]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  have h := quadraticChar_card_sqrts (ringChar_ne_two p hp2) y
  rw [Set.toFinset_card] at h
  rw [χ]
  exact_mod_cast h

theorem χ_mul (a b : ZMod p) : χ p (a * b) = χ p a * χ p b := by
  simp [χ, map_mul]

theorem χ_inv {a : ZMod p} (ha : a ≠ 0) : χ p a⁻¹ = χ p a := by
  have h1 : χ p a⁻¹ * χ p a = 1 := by
    rw [← χ_mul, inv_mul_cancel₀ ha, χ, MulChar.map_one]; simp
  have h2 : χ p a * χ p a = 1 := by
    have := quadraticChar_sq_one ha
    rw [χ]; exact_mod_cast (by rw [← sq]; exact this)
  calc χ p a⁻¹ = χ p a⁻¹ * (χ p a * χ p a) := by rw [h2, mul_one]
    _ = χ p a := by rw [← mul_assoc, h1, one_mul]

/-- `G(b) = (b/p) G(1)`. -/
theorem G_mul (hp2 : p ≠ 2) {b : ZMod p} (hb : b ≠ 0) : G p b = χ p b * G p 1 := by
  have key : ∀ c : ZMod p, c ≠ 0 → G p c = ∑ y : ZMod p, χ p y * ψ p (c * y) := by
    intro c hc
    rw [G, sum_z p (fun x => ψ p (c * x ^ 2)), sum_sq p hp2 (fun y => ψ p (c * y))]
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    rw [sum_ψZ, if_neg hc, add_zero]
  rw [key b hb, key 1 one_ne_zero, Finset.mul_sum]
  have hsq : χ p b * χ p b = 1 := by
    have := quadraticChar_sq_one hb
    rw [χ]; exact_mod_cast (by rw [← sq]; exact this)
  refine Fintype.sum_bijective (fun y => b * y) ?_ _ _ fun y => ?_
  · exact ⟨fun x y h => mul_left_cancel₀ hb h, fun y => ⟨b⁻¹ * y, by field_simp⟩⟩
  · simp only [one_mul]
    rw [χ_mul]
    calc χ p y * ψ p (b * y) = (χ p b * χ p b) * χ p y * ψ p (b * y) := by rw [hsq, one_mul]
      _ = χ p b * (χ p b * χ p y * ψ p (b * y)) := by ring

/-! ### Gauss's sum and `λ_p` -/

theorem G_one (hp2 : p ≠ 2) :
    G p 1 = if p % 4 = 1 then (Real.sqrt p : ℂ) else Complex.I * (Real.sqrt p : ℂ) := by
  rw [← gauss_sum_sign p hp2, G, sum_z p (fun y => ψ p (1 * y ^ 2))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [one_mul, show y ^ 2 = ((y.val ^ 2 : ℕ) : ZMod p) by
    push_cast; rw [ZMod.natCast_zmod_val], ← ωℂ_pow_eq_ψ, ωℂ, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem exp_pi_div_two_I : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]; simp

theorem lambdaP_eq (hp2 : p ≠ 2) : lambdaP p = Complex.I ^ ((p - 1) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := by
    rcases hp.out.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hp2
    · exact ⟨k, by omega⟩
  have hm' : (p - 1 : ℂ) = 2 * m := by
    have : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
      rw [Nat.cast_sub hp.out.one_lt.le]; simp
    rw [← this, hm]; push_cast; ring
  rw [lambdaP, hm', hm, Nat.mul_div_cancel_left _ two_pos]
  conv_rhs => rw [← exp_pi_div_two_I, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-! ### `κ_a = 1` -/

theorem neg_ω_pow_succ (hp2 : p ≠ 2) : (-ωℂ p) ^ (p + 1) = ωℂ p := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rw [neg_pow, (hodd.add_one).neg_one_pow, one_mul, pow_succ, ωℂ_pow_p, one_mul]

theorem neg_ω_pow_p (hp2 : p ≠ 2) : (-ωℂ p) ^ p = -1 := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rw [neg_pow, hodd.neg_one_pow, ωℂ_pow_p, mul_one]

theorem legendre_sign {a : ZMod p} (ha : a ≠ 0) : ((-1 : ℂ)) ^ legendreExp p a = χ p a := by
  have hl : legendreSym p (a.val : ℤ) = quadraticChar (ZMod p) a := by
    rw [legendreSym]; congr 1; push_cast; exact ZMod.natCast_zmod_val a
  rw [legendreExp, hl, χ]
  rcases quadraticChar_dichotomy ha with h | h
  · rw [if_pos h, h]; simp
  · rw [if_neg (by rw [h]; decide), h]; simp

theorem χ_two_eq (hp2 : p ≠ 2) : χ p 2 = (ZMod.χ₈ p : ℂ) := by
  have h : legendreSym p 2 = quadraticChar (ZMod p) 2 := by
    rw [legendreSym]; congr 1; push_cast; rfl
  rw [χ, ← h, legendreSym.at_two hp2]

theorem χ_two_lambda (hp2 : p ≠ 2) :
    χ p 2 * (lambdaP p ^ 3)⁻¹ * (if p % 4 = 1 then 1 else Complex.I) = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  rw [χ_two_eq p hp2, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega), lambdaP_eq p hp2,
    ← pow_mul]
  have hI : ∀ k j : ℕ, Complex.I ^ (4 * k + j) = Complex.I ^ j := by
    intro k j; rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hr with h | h | h | h
  · rw [show (p - 1) / 2 * 3 = 4 * (3 * (p / 8)) + 0 by omega, hI, if_pos (by omega),
      if_pos (by omega)]
    simp
  · rw [show (p - 1) / 2 * 3 = 4 * (3 * (p / 8)) + 3 by omega, hI, if_neg (by omega),
      if_neg (by omega), hI3, inv_neg, Complex.inv_I]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  · rw [show (p - 1) / 2 * 3 = 4 * (3 * (p / 8) + 1) + 2 by omega, hI, if_neg (by omega),
      if_pos (by omega), Complex.I_sq]
    push_cast; norm_num
  · rw [show (p - 1) / 2 * 3 = 4 * (3 * (p / 8) + 2) + 1 by omega, hI, if_pos (by omega),
      if_neg (by omega), pow_one, inv_mul_cancel_right₀ Complex.I_ne_zero]
    push_cast; ring

/-- Lemma 2.15: the scalar of (T1) is `1`, given Gauss's evaluation of the
quadratic Gauss sum. -/
theorem κM_eq_one (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) : κM p a = 1 := by
  have h2 := two_ne_zero' p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h8 : (8 : ZMod p) ≠ 0 := by
    rw [show (8 : ZMod p) = 2 * 4 by norm_num]; exact mul_ne_zero h2 h4
  have hc2 : a⁻¹ / 2 ≠ 0 := div_ne_zero (inv_ne_zero ha) h2
  have hχa : χ p a * χ p a = 1 := by
    have := quadraticChar_sq_one ha
    rw [χ]; exact_mod_cast (by rw [← sq]; exact this)
  have hχc : χ p (a⁻¹ / 2) = χ p a * χ p 2 := by
    rw [div_eq_mul_inv, χ_mul, χ_inv p ha, χ_inv p h2]
  have hpsi : ψ p ((-a ^ 2 + 4 * a - 2) / (8 * a)) *
      ψ p (a⁻¹ * q p (-((1 - a) / 2)) - a * (a⁻¹ / 2) ^ 2 / 2) = 1 := by
    rw [← ψ_add, ← ψ_zero p]; congr 1; simp only [q]; field_simp; ring
  have hsq : (Real.sqrt p : ℂ) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]; simp
  have hs0 : (Real.sqrt p : ℂ) ≠ 0 := by
    intro h; rw [h] at hsq; simp at hsq; exact hp.out.ne_zero (by exact_mod_cast hsq.symm)
  have hl0 := lambdaP_ne_zero p
  have hc3 : hc p ^ 3 * p * (Real.sqrt p : ℂ) = (lambdaP p ^ 3)⁻¹ := by
    rw [hc, ← hsq]; field_simp
  have hkey := χ_two_lambda p hp2
  rw [κM, pow_mul, pow_mul, neg_ω_pow_succ p hp2, neg_ω_pow_p p hp2, legendre_sign p ha,
    ωℂ_pow_eq_ψ, ZMod.natCast_zmod_val, G_mul p hp2 hc2, G_one p hp2, hχc]
  by_cases hp4 : p % 4 = 1
  · rw [if_pos hp4] at hkey ⊢
    calc _ = (ψ p ((-a ^ 2 + 4 * a - 2) / (8 * a)) *
          ψ p (a⁻¹ * q p (-((1 - a) / 2)) - a * (a⁻¹ / 2) ^ 2 / 2)) * (χ p a * χ p a) * χ p 2 *
          (hc p ^ 3 * p * (Real.sqrt p : ℂ)) := by ring
      _ = 1 := by rw [hpsi, hχa, hc3]; linear_combination hkey
  · rw [if_neg hp4] at hkey ⊢
    calc _ = (ψ p ((-a ^ 2 + 4 * a - 2) / (8 * a)) *
          ψ p (a⁻¹ * q p (-((1 - a) / 2)) - a * (a⁻¹ / 2) ^ 2 / 2)) * (χ p a * χ p a) * χ p 2 *
          Complex.I * (hc p ^ 3 * p * (Real.sqrt p : ℂ)) := by ring
      _ = 1 := by rw [hpsi, hχa, hc3]; linear_combination hkey

/-- Lemma 2.15: the circuit (T1) is the multiplier `|x⟩ ↦ |ax⟩`. -/
theorem sem_M_eq (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ((sem p 1 (M p a) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      mono p (multσ p a) fun _ => 1 := by
  rw [sem_M p hp2 a ha, κM_eq_one p hp2 ha, one_smul]

/-- (C2) `H² = M_{-1} · (-1)^{(p-1)/2}` (Proposition 2.13). -/
theorem sound_C2 (hp2 : p ≠ 2) :
    sem p 1 (H ^ 2) = sem p 1 (M p (-1) ⨾ neg1 p ^ ((p - 1) / 2)) := by
  apply Subtype.ext
  rw [seq_def, neg1, ← pow_mul, map_mul, Submonoid.coe_mul, sem1_scalar,
    sem_M_eq p hp2 (neg_ne_zero.mpr one_ne_zero), map_pow, SubmonoidClass.coe_pow, sem_H,
    Hsq_mono, mono_mul, smul_mono, pow_mul, neg_ω_pow_p p hp2, ← lambdaP_sq p hp2]
  apply mono_ext p
  · intro t
    apply state_one_ext p
    show -(t 0) = zinv p (-1 * z p (t 0))
    apply z_injective p
    rw [z_neg, z_zinv]; ring
  · intro t
    have h4 := lambdaP_pow_four p hp2
    have hl := lambdaP_ne_zero p
    simp only [mul_one]
    field_simp
    linear_combination -h4

theorem multσ_iterate (g : ZMod p) (k : ℕ) (t : State p 1) :
    z p ((multσ p g)^[k] t 0) = g ^ k * z p (t 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', multσ, z_zinv, ih, pow_succ]; ring

/-- (C3) `(M_g)^k = M_{g^k}`, `k ∈ ℤ_p`. -/
theorem sound_C3 (hp2 : p ≠ 2) {g : ZMod p} (hg : g ≠ 0) (k : ZMod p) :
    sem p 1 (M p g ^ k.val) = sem p 1 (M p (g ^ k.val)) := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_M_eq p hp2 hg, sem_M_eq p hp2 (pow_ne_zero _ hg),
    mono_one_pow]
  apply mono_ext p
  · intro t
    apply state_one_ext p
    apply z_injective p
    rw [multσ_iterate]; simp [multσ, z_zinv]
  · intro t; rfl

end

end QCert.QuditClifford
