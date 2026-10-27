/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The quadratic Gauss sum from the Jacobi theta function

We evaluate `G(p) = ∑_{r mod p} e^{2πi r²/p}` for every `p ≥ 1`:

  `G(p) = √p (1 + i) / 2 · (1 + e^{-πip/2})`        (`gauss_sum_fin`),

the Landsberg–Schaar identity at `q = 1`, which gives Gauss's `√p` for
`p ≡ 1` and `i √p` for `p ≡ 3 (mod 4)`.  The only analytic input is
Mathlib's functional equation of the two-variable theta function
`θ(z, τ) = ∑_n e^{2πinz + πin²τ}`:

  `θ(z, τ) = (-iτ)^{-1/2} e^{-πiz²/τ} θ(z/τ, -1/τ)`
                                       (`jacobiTheta₂_functional_equation`).

## The proof

1. *A residue class.*  For `c ≥ 1`, `r ∈ ℂ` and `Im w > 0`,
   `∑_m e^{πi(r + cm)² w} = (-i c² w)^{-1/2} θ(r/c, -1/(c² w))`
   (`hasSum_residue`): the left side is `e^{πir²w} θ(crw, c²w)`, and the
   functional equation turns `θ(crw, c²w)` into
   `(-ic²w)^{-1/2} e^{-πir²w} θ(r/c, -1/(c²w))`.

2. *Summing by residues.*  A convergent series over `ℤ` is the sum over
   `r ∈ Fin c` of its subseries over `r + cℤ` (`sum_residues`, through
   `Int.divModEquiv`).

3. *The identity.*  Fix `y > 0` and put `w = i/(p²y)`, `τ = 2/p + w`.
   * Since `e^{πi n² · 2/p}` only depends on `n mod p`, summing
     `θ(0, τ) = ∑_n e^{πin²τ}` by residues mod `p` and using 1 with
     `c = p` (where `-ip²w = 1/y` and `-1/(p²w) = iy`) gives
     `θ(0, τ) = √y ∑_{r < p} e^{2πir²/p} θ(r/p, iy)`.
   * The functional equation at `z = 0` gives
     `θ(0, τ) = (-iτ)^{-1/2} θ(0, -1/τ)`, and `-1/τ = -p/2 + w'` with
     `w' = pi/(2(2py + i))`, `Im w' > 0`.  Now `e^{πin² · (-p/2)}` is `1`
     for `n` even and `e^{-πip/2}` for `n` odd, so summing by residues
     mod `2` and using 1 with `c = 2` (where `-1/(4w') = iy - 1/(2p)`)
     gives `θ(0, -1/τ) = (-4iw')^{-1/2} (θ(0, τ'') + e^{-πip/2} θ(1/2, τ''))`
     with `τ'' = iy - 1/(2p)`.
   * The constants: `(-iτ)(-4iw') = (2/(py)) · (-i)`, and both factors have
     positive real part, so their arguments add up within `(-π, π)` and
     `(-iτ)^{1/2} (-4iw')^{1/2} = (2/(py))^{1/2} (-i)^{1/2}` with
     `(-i)^{1/2} = e^{-πi/4} = (1 - i)/√2` (`mul_cpow_of_re_pos`,
     `ofReal_mul_neg_I_cpow_half`).  Then
     `1/(√y · √(2/(py)) · (1 - i)/√2) = √p (1 + i)/2 = κ`.
   Hence, for every `y > 0` (`main_identity`),

     `∑_{r < p} e^{2πir²/p} θ(r/p, iy) = κ (θ(0, iy - 1/(2p)) + e^{-πip/2} θ(1/2, iy - 1/(2p)))`.

4. *The limit `y → ∞`.*  For real `z`, `θ(z, τ) → 1` as `Im τ → ∞`
   (`tendsto_jacobiTheta₂`): the term `n` has modulus `e^{-πn² Im τ}`, which
   tends to `0` for `n ≠ 0` and is bounded by `e^{-πn²}` once `Im τ ≥ 1`
   (Tannery's theorem, `tendsto_tsum_of_dominated_convergence`).  Every
   theta value in 3 has imaginary part `y`, so the left side tends to
   `G(p)` and the right side to `κ (1 + e^{-πip/2})` (`gauss_sum_fin`).

5. *Gauss's sign* (`QCert.gauss_sum_sign`, in `GaussSign`).  For
   `p = 4k + 1`, `e^{-πip/2} = -i` and `κ (1 - i) = √p`; for `p = 4k + 3`,
   `e^{-πip/2} = i` and `κ (1 + i) = i √p`.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Group.Tannery

open Complex Real Filter Topology

namespace QCert.GaussTheta

/-- Step 1: the theta series over one residue class modulo `c`. -/
lemma hasSum_residue (c : ℕ) (hc : c ≠ 0) (r w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℤ => cexp (π * I * (r + c * m) ^ 2 * w))
      (1 / (-I * (c ^ 2 * w)) ^ (1 / 2 : ℂ) * jacobiTheta₂ (r / c) (-1 / (c ^ 2 * w))) := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have him : 0 < ((c : ℂ) ^ 2 * w).im := by
    have : ((c : ℂ) ^ 2 * w).im = (c : ℝ) ^ 2 * w.im := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.im_ofReal_mul]
    rw [this]
    have : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
    positivity
  have h1 := (hasSum_jacobiTheta₂_term ((c : ℂ) * r * w) him).mul_left
    (cexp (π * I * r ^ 2 * w))
  have h2 : ∀ m : ℤ, cexp (π * I * r ^ 2 * w) *
      jacobiTheta₂_term m ((c : ℂ) * r * w) ((c : ℂ) ^ 2 * w)
      = cexp (π * I * (r + c * m) ^ 2 * w) := by
    intro m
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [h2] at h1
  convert h1 using 1
  rw [jacobiTheta₂_functional_equation ((c : ℂ) * r * w) ((c : ℂ) ^ 2 * w)]
  have h3 : (c : ℂ) * r * w / (c ^ 2 * w) = r / c := by
    field_simp
  have h4 : -π * I * ((c : ℂ) * r * w) ^ 2 / (c ^ 2 * w) = -(π * I * r ^ 2 * w) := by
    field_simp
  rw [h3, h4, Complex.exp_neg]
  have := Complex.exp_ne_zero (π * I * r ^ 2 * w)
  field_simp

/-- Step 2: a convergent series over `ℤ` is the sum of its subseries over the residue
classes modulo `c`. -/
lemma sum_residues (c : ℕ) [NeZero c] {f : ℤ → ℂ} {a : ℂ} (hf : HasSum f a)
    {b : Fin c → ℂ} (hb : ∀ r : Fin c, HasSum (fun m : ℤ => f (m * c + r)) (b r)) :
    a = ∑ r, b r := by
  let e : Fin c × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv c).symm
  have he : ∀ r : Fin c, ∀ m : ℤ, e (r, m) = m * c + r := by
    intro r m
    simp [e, Int.divModEquiv_symm_apply]
  have hf' : HasSum (f ∘ e) a := (e.hasSum_iff).mpr hf
  have hg : HasSum b a := hf'.prod_fiberwise (fun r => by
    simpa [Function.comp, he] using hb r)
  exact (hasSum_fintype b).unique hg |>.symm

/-- Step 4: for real `z`, `θ(z, τ) → 1` as `Im τ → ∞`. -/
lemma tendsto_jacobiTheta₂ (z : ℂ) (hz : z.im = 0) :
    Tendsto (fun τ => jacobiTheta₂ z τ) (comap im atTop) (𝓝 1) := by
  have h1 : (1 : ℂ) = ∑' n : ℤ, if n = 0 then (1 : ℂ) else 0 := by
    rw [tsum_ite_eq]
  rw [h1]
  unfold jacobiTheta₂
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℤ => rexp (-π * (1 * n ^ 2 - 2 * 0 * |n|))) ?_ ?_ ?_
  · simpa using summable_pow_mul_jacobiTheta₂_term_bound 0 one_pos 0
  · intro n
    by_cases hn : n = 0
    · subst hn
      simpa [jacobiTheta₂_term] using tendsto_const_nhds
    · simp only [hn, if_false]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [norm_jacobiTheta₂_term, hz, mul_zero, sub_zero]
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        positivity
      have hneg : -π * (n : ℝ) ^ 2 < 0 := by
        have := Real.pi_pos
        nlinarith
      exact Real.tendsto_exp_atBot.comp
        ((tendsto_comap (f := im)).const_mul_atTop_of_neg hneg)
  · have : ∀ᶠ τ in comap im atTop, (1 : ℝ) ≤ τ.im :=
      (tendsto_comap (f := im)).eventually (eventually_ge_atTop 1)
    filter_upwards [this] with τ hτ n
    exact norm_jacobiTheta₂_term_le one_pos (by simp [hz]) hτ n


/-- `(a b)^s = a^s b^s` when the arguments of `a` and `b` add up within `(-π, π]`. -/
lemma mul_cpow_of_arg {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : arg a + arg b ∈ Set.Ioc (-π) π) (s : ℂ) : (a * b) ^ s = a ^ s * b ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero ha hb), cpow_def_of_ne_zero ha, cpow_def_of_ne_zero hb,
    (log_mul_eq_add_log_iff ha hb).mpr h, add_mul, Complex.exp_add]

/-- `(a b)^s = a^s b^s` when `a` and `b` have positive real part. -/
lemma mul_cpow_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (s : ℂ) :
    (a * b) ^ s = a ^ s * b ^ s := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  apply mul_cpow_of_arg ha0 hb0
  have h1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have h2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  rw [abs_lt] at h1 h2
  constructor <;> linarith [Real.pi_pos]

/-- The principal square root of a nonnegative real is its real square root. -/
lemma ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow hx]
  norm_num

/-- `(-i)^{1/2} = e^{-πi/4} = (1 - i)/√2`. -/
lemma neg_I_cpow_half : (-I) ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I) := by
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero)]
  have : log (-I) * (1 / 2) = ((-(π / 4) : ℝ) : ℂ) * I := by
    rw [log_neg_I]; push_cast; ring
  rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

/-- `(r · (-i))^{1/2} = √r · (1 - i)/√2` for `r > 0`. -/
lemma ofReal_mul_neg_I_cpow_half {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * (-I)) ^ (1 / 2 : ℂ) = (Real.sqrt r : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I)) := by
  rw [mul_cpow_of_arg (ofReal_ne_zero.mpr hr.ne') (neg_ne_zero.mpr I_ne_zero),
    ofReal_cpow_half hr.le, neg_I_cpow_half]
  rw [arg_ofReal_of_nonneg hr.le, arg_neg_I]
  constructor <;> linarith [Real.pi_pos]

/-- The constant `√p (1 + i) / 2`. -/
noncomputable def kappa (p : ℕ) : ℂ := (Real.sqrt p : ℂ) * (1 + I) / 2


/-- Step 3: the identity behind the Landsberg–Schaar relation at `q = 1`. -/
theorem main_identity (p : ℕ) (hp : p ≠ 0) (y : ℝ) (hy : 0 < y) :
    ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) * jacobiTheta₂ ((r : ℂ) / p) (I * y) =
      kappa p * (jacobiTheta₂ 0 (I * y - 1 / (2 * p)) +
        cexp (-π * I * p / 2) * jacobiTheta₂ (1 / 2) (I * y - 1 / (2 * p))) := by
  haveI : NeZero p := ⟨hp⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  obtain ⟨D, hD⟩ : ∃ D : ℂ, D = 2 * (p : ℂ) * y + I := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    intro h
    have := congrArg im (hD.symm.trans h)
    simp at this
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = I / ((p : ℂ) ^ 2 * y) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℂ, τ = 2 / (p : ℂ) + w := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : ℂ, w' = (p : ℂ) * I / (2 * D) := ⟨_, rfl⟩
  have hτD : τ = D / ((p : ℂ) ^ 2 * y) := by
    rw [hτ, hw, hD]; field_simp
  have hw_im : 0 < w.im := by
    have : w = ((1 / ((p : ℝ) ^ 2 * y) : ℝ) : ℂ) * I := by
      rw [hw]; push_cast; ring
    rw [this]
    simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]
    exact one_div_pos.mpr (mul_pos (pow_pos hpR 2) hy)
  have hτ_im : 0 < τ.im := by
    have : τ.im = w.im := by
      rw [hτ, add_im]
      have : (2 / (p : ℂ)) = ((2 / (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this, ofReal_im, zero_add]
    rw [this]; exact hw_im
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ_im
  have hneg1 : -1 / τ = -(p : ℂ) / 2 + w' := by
    rw [hτD, hw']; field_simp; rw [hD]; ring
  have hinv_im : 0 < (-1 / τ).im := by
    have : (-1 / τ).im = τ.im / normSq τ := by simp [div_im]; ring
    rw [this]; exact div_pos hτ_im (normSq_pos.mpr hτ0)
  have hw'_im : 0 < w'.im := by
    have : w' = -1 / τ + ((p / 2 : ℝ) : ℂ) := by rw [hneg1]; push_cast; ring
    rw [this, add_im, ofReal_im, add_zero]; exact hinv_im
  -- the two ways of summing `θ(0, τ)`
  have hL : jacobiTheta₂ 0 τ = ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) *
      (1 / (-I * ((p : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) *
        jacobiTheta₂ ((r : ℂ) / p) (-1 / ((p : ℂ) ^ 2 * w))) := by
    apply sum_residues p (hasSum_jacobiTheta₂_term 0 hτ_im)
    intro r
    have h := (hasSum_residue p hp (r : ℂ) w hw_im).mul_left (cexp (2 * π * I * (r : ℂ) ^ 2 / p))
    convert h using 1
    funext m
    simp only [jacobiTheta₂_term]
    rw [← Complex.exp_add, exp_eq_exp_iff_exists_int]
    refine ⟨m ^ 2 * p + 2 * m * r, ?_⟩
    rw [hτ]; push_cast; field_simp; ring
  have hR : jacobiTheta₂ 0 τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) *
      (1 / (-I * (2 ^ 2 * w')) ^ (1 / 2 : ℂ) * (jacobiTheta₂ 0 (-1 / (2 ^ 2 * w')) +
        cexp (-π * I * p / 2) * jacobiTheta₂ (1 / 2) (-1 / (2 ^ 2 * w')))) := by
    rw [jacobiTheta₂_functional_equation 0 τ]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      Complex.exp_zero, mul_one]
    congr 1
    have h2 := sum_residues 2 (hasSum_jacobiTheta₂_term 0 hinv_im) (b := fun r : Fin 2 =>
      cexp (-π * I * p * (r : ℂ) ^ 2 / 2) * (1 / (-I * (2 ^ 2 * w')) ^ (1 / 2 : ℂ) *
        jacobiTheta₂ ((r : ℂ) / 2) (-1 / (2 ^ 2 * w')))) (fun r => by
      have h := (hasSum_residue 2 two_ne_zero (r : ℂ) w' hw'_im).mul_left
        (cexp (-π * I * p * (r : ℂ) ^ 2 / 2))
      simp only [Nat.cast_ofNat] at h
      convert h using 1
      funext m
      simp only [jacobiTheta₂_term]
      rw [← Complex.exp_add, exp_eq_exp_iff_exists_int]
      refine ⟨-(p * m ^ 2 + p * m * r), ?_⟩
      rw [hneg1]; push_cast; field_simp; ring)
    rw [h2, Fin.sum_univ_two]
    simp
    ring
  -- the constants
  have hpw : -I * ((p : ℂ) ^ 2 * w) = ((1 / y : ℝ) : ℂ) := by
    rw [hw]; push_cast; field_simp; linear_combination -I_sq
  have hpw2 : -1 / ((p : ℂ) ^ 2 * w) = I * y := by
    rw [hw]; field_simp; linear_combination -I_sq
  have h4w' : -1 / ((2 : ℂ) ^ 2 * w') = I * y - 1 / (2 * p) := by
    rw [hw']; field_simp; rw [hD]; linear_combination (-2 * (p : ℂ) * y) * I_sq
  have hprod : (-I * τ) * (-I * (2 ^ 2 * w')) = ((2 / (p * y) : ℝ) : ℂ) * (-I) := by
    rw [hτD, hw']; push_cast; field_simp; linear_combination I_sq
  have hre1 : 0 < (-I * τ).re := by simpa using hτ_im
  have hre2 : 0 < (-I * (2 ^ 2 * w')).re := by
    have h := mul_pos (by norm_num : (0 : ℝ) < 4) hw'_im
    convert h using 1
    norm_num [mul_re, mul_im]
  have hc1 : (-I * ((p : ℂ) ^ 2 * w)) ^ (1 / 2 : ℂ) = (Real.sqrt (1 / y) : ℂ) := by
    rw [hpw, ofReal_cpow_half (by positivity)]
  have hc2 : (-I * τ) ^ (1 / 2 : ℂ) * (-I * (2 ^ 2 * w')) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 / (p * y)) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I)) := by
    rw [← mul_cpow_of_re_pos hre1 hre2, hprod,
      ofReal_mul_neg_I_cpow_half (div_pos two_pos (mul_pos hpR hy))]
  have hreal : Real.sqrt p * Real.sqrt (2 / (p * y)) * Real.sqrt 2 = 2 * Real.sqrt (1 / y) := by
    rw [← Real.sqrt_mul hpR.le, ← Real.sqrt_mul (mul_pos hpR (div_pos two_pos (mul_pos hpR hy))).le]
    rw [show (p : ℝ) * (2 / (p * y)) * 2 = 2 ^ 2 * (1 / y) by field_simp]
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hκ : kappa p * ((Real.sqrt (2 / (p * y)) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I))) =
      (Real.sqrt (1 / y) : ℂ) := by
    have h1 : (Real.sqrt p : ℂ) * (Real.sqrt (2 / (p * y)) : ℂ) * (Real.sqrt 2 : ℂ) =
        2 * (Real.sqrt (1 / y) : ℂ) := by exact_mod_cast hreal
    unfold kappa
    push_cast
    linear_combination ((1 + I) * (1 - I) / 4) * h1 - ((Real.sqrt (1 / y) : ℂ) / 2) * I_sq
  have hs0 : (Real.sqrt (1 / y) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (one_div_pos.mpr hy)).ne'
  have hA0 : ((Real.sqrt (2 / (p * y)) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I))) ≠ 0 := by
    rw [← hc2]
    exact mul_ne_zero (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr
      (by rintro h; simp [h] at hre1))
      (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.mpr (by rintro h; simp [h] at hre2))
  rw [hpw2, hc1] at hL
  rw [h4w'] at hR
  have key := hL.symm.trans hR
  have hsum : ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) *
      (1 / (Real.sqrt (1 / y) : ℂ) * jacobiTheta₂ ((r : ℂ) / p) (I * y)) =
      1 / (Real.sqrt (1 / y) : ℂ) *
        ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) * jacobiTheta₂ ((r : ℂ) / p) (I * y) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [hsum] at key
  generalize (∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) *
    jacobiTheta₂ ((r : ℂ) / p) (I * y)) = S at key ⊢
  generalize (jacobiTheta₂ 0 (I * y - 1 / (2 * p)) +
    cexp (-π * I * p / 2) * jacobiTheta₂ (1 / 2) (I * y - 1 / (2 * p))) = M at key ⊢
  have key' : 1 / (Real.sqrt (1 / y) : ℂ) * S =
      1 / ((Real.sqrt (2 / (p * y)) : ℂ) * (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - I))) * M := by
    rw [key, ← hc2]; ring
  calc S = (Real.sqrt (1 / y) : ℂ) * (1 / (Real.sqrt (1 / y) : ℂ) * S) := by field_simp
    _ = _ := by
      have hA1 : (Real.sqrt (2 / (p * y)) : ℂ) ≠ 0 := (mul_ne_zero_iff.mp hA0).1
      have hB1 : (1 - I) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hA0).2).2
      rw [key', ← hκ]; field_simp


/-- Step 4: the quadratic Gauss sum modulo any `p ≥ 1`,
`∑_{r < p} e^{2πir²/p} = √p (1 + i)/2 · (1 + e^{-πip/2})`. -/
theorem gauss_sum_fin (p : ℕ) (hp : p ≠ 0) :
    ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) = kappa p * (1 + cexp (-π * I * p / 2)) := by
  have hpath1 : Tendsto (fun y : ℝ => I * (y : ℂ)) atTop (comap im atTop) := by
    rw [tendsto_comap_iff]
    refine tendsto_id.congr (fun y => ?_)
    simp
  have hpath2 : Tendsto (fun y : ℝ => I * (y : ℂ) - 1 / (2 * p)) atTop (comap im atTop) := by
    rw [tendsto_comap_iff]
    refine tendsto_id.congr (fun y => ?_)
    have : (1 / (2 * (p : ℂ))) = ((1 / (2 * p) : ℝ) : ℂ) := by push_cast; ring
    show y = (I * (y : ℂ) - 1 / (2 * p)).im
    rw [sub_im, this, ofReal_im, sub_zero]
    simp
  have hL : Tendsto (fun y : ℝ => ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) *
      jacobiTheta₂ ((r : ℂ) / p) (I * y)) atTop
      (𝓝 (∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) * 1)) := by
    apply tendsto_finsetSum
    intro r _
    refine tendsto_const_nhds.mul ((tendsto_jacobiTheta₂ _ ?_).comp hpath1)
    have : ((r : ℂ) / p) = (((r : ℝ) / p : ℝ) : ℂ) := by push_cast; ring
    rw [this, ofReal_im]
  have hR : Tendsto (fun y : ℝ => kappa p * (jacobiTheta₂ 0 (I * y - 1 / (2 * p)) +
        cexp (-π * I * p / 2) * jacobiTheta₂ (1 / 2) (I * y - 1 / (2 * p)))) atTop
      (𝓝 (kappa p * (1 + cexp (-π * I * p / 2) * 1))) := by
    refine tendsto_const_nhds.mul (((tendsto_jacobiTheta₂ 0 (by simp)).comp hpath2).add
      (tendsto_const_nhds.mul ((tendsto_jacobiTheta₂ (1 / 2) ?_).comp hpath2)))
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ofReal_im]
  have heq : (fun y : ℝ => ∑ r : Fin p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) *
      jacobiTheta₂ ((r : ℂ) / p) (I * y)) =ᶠ[atTop] (fun y : ℝ => kappa p *
        (jacobiTheta₂ 0 (I * y - 1 / (2 * p)) +
          cexp (-π * I * p / 2) * jacobiTheta₂ (1 / 2) (I * y - 1 / (2 * p)))) := by
    filter_upwards [eventually_gt_atTop 0] with y hy using main_identity p hp y hy
  have := tendsto_nhds_unique (hL.congr' heq) hR
  simpa using this

end QCert.GaussTheta
