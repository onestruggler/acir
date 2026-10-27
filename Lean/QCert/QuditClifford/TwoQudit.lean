/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The swap and `CX` as permutations (Lemmas A.18, A.20)

The circuits (T4) and (T6) are the permutations `|j, ℓ⟩ ↦ |ℓ, j⟩` and
`|j, ℓ⟩ ↦ |j, ℓ + j⟩` (control on the top wire), by path sums: each
reduces to character sums `∑_u ψ (a u) = p [a = 0]`, and the scalars
cancel because `λ_p⁴ = 1` and `λ_p² = (-1)^{(p-1)/2}`.

Two-qudit basis states are `![x₀, x₁]`, `x₀` on wire 0 (the bottom wire).
-/
import QCert.QuditClifford.PathSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ### `λ_p` -/

theorem lambdaP_sq (hp2 : p ≠ 2) : lambdaP p ^ 2 = (-1) ^ ((p - 1) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := by
    rcases hp.out.eq_two_or_odd' with h | ⟨k, hk⟩
    · exact absurd h hp2
    · exact ⟨k, by omega⟩
  have hm' : (p - 1 : ℂ) = 2 * m := by
    have : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
      rw [Nat.cast_sub hp.out.one_lt.le]; simp
    rw [← this, hm]; push_cast; ring
  rw [lambdaP, ← Complex.exp_nat_mul, hm', hm, Nat.mul_div_cancel_left _ two_pos,
    show ((2 : ℕ) : ℂ) * (2 * m * Real.pi * Complex.I / 4) = m * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem lambdaP_pow_four (hp2 : p ≠ 2) : lambdaP p ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, lambdaP_sq p hp2, ← pow_mul, mul_comm, pow_mul,
    neg_one_sq, one_pow]

omit hp in
theorem lambdaP_ne_zero : lambdaP p ≠ 0 := Complex.exp_ne_zero _

omit hp in
theorem hc_sq : hc p ^ 2 = (lambdaP p ^ 2)⁻¹ * (p : ℂ)⁻¹ := by
  rw [hc, inv_pow, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), mul_inv]
  simp

/-! ### Two-qudit states -/

omit hp in
theorem state2_eq (s : State p 2) : s = ![s 0, s 1] := by
  funext i; fin_cases i <;> rfl

omit hp in
theorem sum_state2 (f : State p 2 → ℂ) :
    ∑ u, f u = ∑ x0 : Fin p, ∑ x1 : Fin p, f ![x0, x1] := by
  rw [← (piFinTwoEquiv fun _ => Fin p).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x0 _ => Finset.sum_congr rfl fun x1 _ => congrArg f ?_
  funext i; fin_cases i <;> rfl

omit hp in
theorem onTop_two (A : Op ℂ p 1) (s t : State p 2) :
    onTop 1 A s t = if s 0 = t 0 then A (fun _ => s 1) (fun _ => t 1) else 0 := by
  rw [onTop_apply]
  have h1 : (split p 1 1 s).1 = (split p 1 1 t).1 ↔ s 0 = t 0 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
  have h2 : ∀ u : State p 2, (split p 1 1 u).2 = fun _ => u 1 := by
    intro u; funext j; rw [Subsingleton.elim j 0]; rfl
  simp only [h1, h2]

omit hp in
theorem onBottom_two (A : Op ℂ p 1) (s t : State p 2) :
    onBottom (n := 1) A s t = if s 1 = t 1 then A (fun _ => s 0) (fun _ => t 0) else 0 := by
  rw [onBottom_apply]
  have h1 : (split p 1 1 s).2 = (split p 1 1 t).2 ↔ s 1 = t 1 := by
    constructor
    · intro h; exact congrFun h 0
    · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
  have h2 : ∀ u : State p 2, (split p 1 1 u).1 = fun _ => u 0 := by
    intro u; funext j; rw [Subsingleton.elim j 0]; rfl
  simp only [h1, h2]

/-! ### Character sums over two digits -/

theorem sum_bilin (A B c : ZMod p) :
    ∑ x0 : Fin p, ∑ x1 : Fin p, ψ p (z p x0 * (A + z p x1) + z p x1 * B + c) =
      p * ψ p (c - A * B) := by
  rw [Finset.sum_comm]
  have : ∀ x1 : Fin p, ∑ x0 : Fin p, ψ p (z p x0 * (A + z p x1) + z p x1 * B + c) =
      ψ p (z p x1 * B + c) * (if A + z p x1 = 0 then (p : ℂ) else 0) := by
    intro x1
    rw [← sum_ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x0 _ => ?_
    rw [← ψ_add]; congr 1; ring
  simp_rw [this, mul_ite, mul_zero]
  simp_rw [show ∀ x1 : Fin p, (A + z p x1 = 0) ↔ z p x1 = -A from fun x1 => by
    constructor <;> intro h <;> linear_combination h]
  rw [sum_ite_z, z_zinv, mul_comm]; congr 2; ring

theorem sum_lin (A B c : ZMod p) :
    ∑ x0 : Fin p, ∑ x1 : Fin p, ψ p (z p x0 * A + z p x1 * B + c) =
      if A = 0 ∧ B = 0 then (p : ℂ) ^ 2 * ψ p c else 0 := by
  have : ∀ x0 : Fin p, ∑ x1 : Fin p, ψ p (z p x0 * A + z p x1 * B + c) =
      ψ p (z p x0 * A + c) * (if B = 0 then (p : ℂ) else 0) := by
    intro x0
    rw [← sum_ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [← ψ_add]; congr 1; ring
  simp_rw [this, ← Finset.sum_mul]
  have h2 : ∑ x0 : Fin p, ψ p (z p x0 * A + c) = ψ p c * (if A = 0 then (p : ℂ) else 0) := by
    rw [← sum_ψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x0 _ => ?_
    rw [← ψ_add]; congr 1; ring
  rw [h2]
  by_cases hA : A = 0 <;> by_cases hB : B = 0 <;> simp [hA, hB] <;> ring

/-! ### `H ⊗ H` and the swap -/

/-- `H` on both wires. -/
def HH : Op ℂ p 2 := onTop 1 (Hop p) * onBottom (n := 1) (Hop p)

theorem HH_apply (s t : State p 2) :
    HH p s t = hc p ^ 2 * ψ p (z p (s 1) * z p (t 1) + z p (s 0) * z p (t 0)) := by
  rw [HH, mul_apply, sum_state2]
  simp only [onTop_two, onBottom_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (s 0)]
  · rw [Finset.sum_eq_single (t 1)]
    · simp only [if_true, Hop_apply]
      rw [pow_two, ψ_add, mul_comm (z p (s 1)), mul_comm (z p (s 0))]
      ring
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Ne.symm hb]
  · simp

omit hp in
theorem cons2_zero (x0 x1 : Fin p) : (![x0, x1] : State p 2) 0 = x0 := rfl

omit hp in
theorem cons2_one (x0 x1 : Fin p) : (![x0, x1] : State p 2) 1 = x1 := rfl

theorem CZ_entry (u : State p 2) :
    ωℂ p ^ ((u 1).val * (u 0).val) = ψ p (z p (u 1) * z p (u 0)) := by
  rw [ωℂ_pow_eq_ψ, Nat.cast_mul]; rfl

theorem ψψψ (c : ℂ) (a b d : ZMod p) :
    c * ψ p a * ψ p b * (c * ψ p d) = c ^ 2 * ψ p (a + b + d) := by
  rw [ψ_add, ψ_add]; ring

/-- `(H ⊗ H) CZ (H ⊗ H)`. -/
theorem G_apply (s t : State p 2) :
    (HH p * CZop p * HH p) s t =
      hc p ^ 4 * p * ψ p (0 - (z p (s 0) + z p (t 0)) * (z p (s 1) + z p (t 1))) := by
  rw [mul_apply, sum_state2]
  have key : ∀ x0 x1 : Fin p, (HH p * CZop p) s ![x0, x1] * HH p ![x0, x1] t =
      hc p ^ 4 * ψ p (z p x0 * ((z p (s 0) + z p (t 0)) + z p x1) +
        z p x1 * (z p (s 1) + z p (t 1)) + 0) := by
    intro x0 x1
    rw [CZop, mul_diagonal, HH_apply, HH_apply, CZ_entry]
    simp only [cons2_zero, cons2_one]
    rw [ψψψ, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    congr 2; ring
  simp_rw [key, ← Finset.mul_sum]
  rw [sum_bilin]; ring

/-- `CZ (H ⊗ H) CZ (H ⊗ H) CZ (H ⊗ H)`: `|j, ℓ⟩ ↦ λ_p⁻⁶ |ℓ, j⟩`. -/
theorem W_apply (s t : State p 2) :
    (CZop p * (HH p * CZop p * HH p) * CZop p * HH p) s t =
      if t 0 = s 1 ∧ t 1 = s 0 then hc p ^ 6 * p ^ 3 else 0 := by
  rw [mul_apply, sum_state2]
  have key : ∀ x0 x1 : Fin p, (CZop p * (HH p * CZop p * HH p) * CZop p) s ![x0, x1] *
      HH p ![x0, x1] t = hc p ^ 6 * p * ψ p (z p (s 1) * z p (s 0)) *
      ψ p (z p x0 * (z p (t 0) - z p (s 1)) + z p x1 * (z p (t 1) - z p (s 0)) +
        -(z p (s 0) * z p (s 1))) := by
    intro x0 x1
    rw [CZop, mul_diagonal, diagonal_mul, ← CZop, G_apply, HH_apply, CZ_entry, CZ_entry]
    simp only [cons2_zero, cons2_one]
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add]
    have : ∀ a b c d : ZMod p, ψ p a * (hc p ^ 4 * p * ψ p b) * ψ p c * (hc p ^ 2 * ψ p d) =
        hc p ^ 4 * hc p ^ 2 * p * ψ p a * ψ p (b + c + d) := by
      intro a b c d; rw [ψ_add, ψ_add]; ring
    rw [this]; congr 2; ring
  simp_rw [key, ← Finset.mul_sum]
  rw [sum_lin]
  by_cases h : t 0 = s 1 ∧ t 1 = s 0
  · have h' : z p (t 0) - z p (s 1) = 0 ∧ z p (t 1) - z p (s 0) = 0 := by
      rw [h.1, h.2]; simp
    rw [if_pos h', if_pos h]
    have := ψ_neg_mul_self p (z p (s 1) * z p (s 0))
    rw [mul_comm (z p (s 0)) (z p (s 1))]
    linear_combination (hc p ^ 6 * p ^ 3) * this
  · have h' : ¬ (z p (t 0) - z p (s 1) = 0 ∧ z p (t 1) - z p (s 0) = 0) := by
      rintro ⟨h1, h2⟩
      exact h ⟨z_injective p (sub_eq_zero.1 h1), z_injective p (sub_eq_zero.1 h2)⟩
    rw [if_neg h', if_neg h, mul_zero]

/-- The swap permutation `|j, ℓ⟩ ↦ |ℓ, j⟩`. -/
def swap2 (t : State p 2) : State p 2 := ![t 1, t 0]

theorem sem_HH : ((sem p 2 (par H H) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = HH p := by
  show ((sem p 2 (Circuit.shift H * Circuit.pad 1 H) : unitaryGroup (State p 2) ℂ) :
    Op ℂ p 2) = _
  have h2 : ((sem p 2 (Circuit.pad 1 H) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) =
      onBottom (n := 1) (Hop p) := by
    have := congrArg Subtype.val ((gateSem p).sem_pad 1 H)
    exact this.trans (by show onBottom _ = _; rw [sem_H])
  rw [map_mul, Submonoid.coe_mul, (gateSem p).sem_shift, h2]
  show onTop 1 _ * _ = _
  rw [sem_H]; rfl

theorem sem_scalar_pow {n : ℕ} (k : ℕ) :
    ((sem p n (negω ^ k) : unitaryGroup (State p n) ℂ) : Op ℂ p n) = (-ωℂ p) ^ k • 1 := by
  rw [map_pow, SubmonoidClass.coe_pow, sem_negω, diagonal_pow]
  ext s t; by_cases h : s = t <;> simp [h]

theorem swap_const (hp2 : p ≠ 2) :
    (-ωℂ p) ^ (p * ((p - 1) / 2)) * (hc p ^ 6 * p ^ 3) = 1 := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have h4 := lambdaP_pow_four p hp2
  have hl := lambdaP_ne_zero p
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [pow_mul, neg_pow, ωℂ_pow_p, mul_one, hodd.neg_one_pow, ← lambdaP_sq p hp2,
    show hc p ^ 6 = (hc p ^ 2) ^ 3 by ring, hc_sq]
  field_simp
  linear_combination -h4

/-- Lemma A.20: the circuit (T4) is the swap `|j, ℓ⟩ ↦ |ℓ, j⟩`. -/
theorem sem_SWAP (hp2 : p ≠ 2) :
    ((sem p 2 (SWAP p) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = mono p (swap2 p) fun _ => 1 := by
  simp only [SWAP, neg1, seq_def, map_mul, Submonoid.coe_mul, sem_HH, sem_CZ, ← pow_mul,
    sem_scalar_pow]
  rw [smul_mul_assoc, one_mul]
  have e : CZop p * (HH p * (CZop p * (HH p * (CZop p * HH p)))) =
      CZop p * (HH p * CZop p * HH p) * CZop p * HH p := by simp only [mul_assoc]
  rw [e]
  ext s t
  rw [smul_apply, smul_eq_mul, W_apply, mono, swap2]
  have hst : s = ![t 1, t 0] ↔ t 0 = s 1 ∧ t 1 = s 0 := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩; rw [state2_eq p s, ← h0, ← h1]
  by_cases h : t 0 = s 1 ∧ t 1 = s 0
  · rw [if_pos h, if_pos (hst.2 h), swap_const p hp2]
  · rw [if_neg h, if_neg (fun h' => h (hst.1 h')), mul_zero]

omit hp in
theorem swap2_swap2 (t : State p 2) : swap2 p (swap2 p t) = t := by
  rw [swap2, swap2]; exact (state2_eq p t).symm

omit hp in
theorem mono_one_mul_apply {n : ℕ} (σ : State p n → State p n) (hσ : ∀ x, σ (σ x) = x)
    (M : Op ℂ p n) (s t : State p n) : (mono p σ (fun _ => 1) * M) s t = M (σ s) t := by
  rw [mul_apply, Finset.sum_eq_single (σ s)]
  · simp [mono, hσ]
  · intro u _ hu
    have : s ≠ σ u := fun h => hu (by rw [h, hσ])
    simp [mono, this]
  · simp

omit hp in
theorem mul_mono_one_apply {n : ℕ} (σ : State p n → State p n) (M : Op ℂ p n)
    (s t : State p n) : (M * mono p σ (fun _ => 1)) s t = M s (σ t) := by
  rw [mul_apply, Finset.sum_eq_single (σ t)]
  · simp [mono]
  · intro u _ hu; simp [mono, hu]
  · simp

omit hp in
/-- The swap carries a gate on the top wire to the bottom wire. -/
theorem swap_onTop (A : Op ℂ p 1) :
    mono p (swap2 p) (fun _ => 1) * onTop 1 A = onBottom (n := 1) A * mono p (swap2 p) fun _ => 1 := by
  ext s t
  rw [mono_one_mul_apply p _ (swap2_swap2 p), mul_mono_one_apply, onTop_two, onBottom_two]
  simp only [swap2, cons2_zero, cons2_one]

theorem Hop_cube_apply (s t : State p 1) :
    (Hop p ^ 3) s t = (lambdaP p ^ 2)⁻¹ * (hc p * ψ p (-(z p (s 0) * z p (t 0)))) := by
  rw [pow_succ, sq, Hop_sq, smul_mul_assoc, smul_apply, smul_eq_mul, mul_apply]
  congr 1
  rw [Finset.sum_eq_single (fun _ => -(s 0))]
  · rw [Pneg, if_pos (by simp), one_mul, Hop_apply, z_neg]; congr 2; ring
  · intro u _ hu
    rw [Pneg, if_neg, zero_mul]
    intro h; exact hu (state_one_ext p (by show u 0 = -(s 0); rw [h, neg_neg]))
  · simp

theorem sem_bot (c : Circ 1) :
    ((sem p 2 (bot c) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) =
      onBottom (n := 1) ((sem p 1 c : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) :=
  congrArg Subtype.val ((gateSem p).sem_pad 1 c)

theorem sem_top {n : ℕ} (c : Circ n) :
    ((sem p (n + 1) (top c) : unitaryGroup (State p (n + 1)) ℂ) : Op ℂ p (n + 1)) =
      onTop 1 ((sem p n c : unitaryGroup (State p n) ℂ) : Op ℂ p n) :=
  congrArg Subtype.val ((gateSem p).sem_shift c)

/-- `CX |j, ℓ⟩ = |j, ℓ + j⟩`, control `j` on wire 1. -/
def cx2 (t : State p 2) : State p 2 := ![t 0 + t 1, t 1]

theorem cx_const (hp2 : p ≠ 2) : (lambdaP p ^ 2)⁻¹ * hc p ^ 2 * p = 1 := by
  have h4 := lambdaP_pow_four p hp2
  have hl := lambdaP_ne_zero p
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hc_sq]; field_simp; linear_combination -h4

/-- Lemma A.18: the circuit (T6) is `|j, ℓ⟩ ↦ |j, ℓ + j⟩`. -/
theorem sem_CX (hp2 : p ≠ 2) :
    ((sem p 2 CX : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = mono p (cx2 p) fun _ => 1 := by
  rw [CX, seq_def, seq_def, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, sem_bot,
    sem_bot, sem_CZ, map_pow, SubmonoidClass.coe_pow, sem_H]
  ext s t
  rw [mul_apply, sum_state2]
  have key : ∀ x0 x1 : Fin p, onBottom (n := 1) (Hop p ^ 3) s ![x0, x1] *
      (CZop p * onBottom (n := 1) (Hop p)) ![x0, x1] t =
      if x1 = s 1 ∧ x1 = t 1 then
        (lambdaP p ^ 2)⁻¹ * hc p ^ 2 * ψ p (z p x0 * (z p (t 0) + z p x1 - z p (s 0))) else 0 := by
    intro x0 x1
    rw [CZop, diagonal_mul, onBottom_two, onBottom_two, CZ_entry]
    simp only [cons2_zero, cons2_one, Hop_cube_apply, Hop_apply]
    by_cases h : x1 = s 1 ∧ x1 = t 1
    · obtain ⟨h1, h2⟩ := h
      rw [if_pos h1.symm, if_pos h2, if_pos ⟨h1, h2⟩]
      have : ∀ a b c : ZMod p, (lambdaP p ^ 2)⁻¹ * (hc p * ψ p a) * (ψ p b * (hc p * ψ p c)) =
          (lambdaP p ^ 2)⁻¹ * hc p ^ 2 * ψ p (a + b + c) := by
        intro a b c; rw [ψ_add, ψ_add]; ring
      rw [this]; congr 2; ring
    · rw [if_neg h]
      by_cases h1 : x1 = s 1
      · have h2 : ¬ x1 = t 1 := fun h2 => h ⟨h1, h2⟩
        rw [if_neg h2]; ring
      · rw [if_neg (Ne.symm h1)]; ring
  simp_rw [key]
  have inner : ∀ x0 : Fin p, (∑ x1 : Fin p, if x1 = s 1 ∧ x1 = t 1 then
      (lambdaP p ^ 2)⁻¹ * hc p ^ 2 * ψ p (z p x0 * (z p (t 0) + z p x1 - z p (s 0))) else 0) =
      if s 1 = t 1 then (lambdaP p ^ 2)⁻¹ * hc p ^ 2 *
        ψ p ((z p (t 0) + z p (t 1) - z p (s 0)) * z p x0) else 0 := by
    intro x0
    rw [Finset.sum_eq_single (s 1)]
    · by_cases h : s 1 = t 1
      · rw [if_pos ⟨rfl, h⟩, if_pos h, h, mul_comm (z p x0)]
      · rw [if_neg (fun h' => h h'.2), if_neg h]
    · intro b _ hb; rw [if_neg (fun h => hb h.1)]
    · simp
  simp_rw [inner]
  rw [mono, cx2]
  have hst : s = ![t 0 + t 1, t 1] ↔ s 1 = t 1 ∧ z p (t 0) + z p (t 1) - z p (s 0) = 0 := by
    constructor
    · rintro rfl; refine ⟨rfl, ?_⟩; simp [z_add]
    · rintro ⟨h1, h2⟩
      rw [state2_eq p s, h1]
      congr 2
      exact z_injective p (by rw [z_add]; linear_combination -h2)
  by_cases h1 : s 1 = t 1
  · simp only [if_pos h1]
    rw [← Finset.mul_sum, sum_ψ]
    by_cases h2 : z p (t 0) + z p (t 1) - z p (s 0) = 0
    · rw [if_pos h2, if_pos (hst.2 ⟨h1, h2⟩), cx_const p hp2]
    · rw [if_neg h2, if_neg (fun h => h2 (hst.1 h).2), mul_zero]
  · simp only [if_neg h1, Finset.sum_const_zero]
    rw [if_neg (fun h => h1 (hst.1 h).1)]

end

end QCert.QuditClifford
