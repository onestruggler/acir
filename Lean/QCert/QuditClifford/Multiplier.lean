/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Pauli gates and multipliers (Lemmas A.15, A.16, 2.15)

* `sem_Z`: the circuit (T3) is `Z |j⟩ = ω^j |j⟩`;
* `sem_X`: the circuit (T2) is `X |j⟩ = |j + 1⟩`;
* `sem_M`: for `a ≠ 0` the circuit (T1) is a scalar multiple of the
  multiplier `|x⟩ ↦ |ax⟩`.  The path sum, after completing the square,
  leaves one quadratic Gauss sum `G(a⁻¹/2)` in the scalar; that the scalar
  is `1` (Lemma 2.15) is Gauss's evaluation of the sign of `G(1)`, which is
  not needed here: (C4) and (C9) have one multiplier on each side.
-/
import QCert.QuditClifford.ThreeQudit

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

omit hp in
theorem sum_state1 (f : State p 1 → ℂ) : ∑ u, f u = ∑ x : Fin p, f fun _ => x := by
  rw [← (Equiv.funUnique (Fin 1) (Fin p)).symm.sum_comp]; rfl

omit hp in
/-- `M_{-1}` as a monomial operator. -/
theorem Pneg_mono : Pneg p = mono p (fun t => fun _ => -(t 0)) fun _ => 1 := by
  ext s t
  simp only [Pneg, mono]
  by_cases h : s 0 = -(t 0)
  · rw [if_pos h, if_pos (state_one_ext p h)]
  · rw [if_neg h, if_neg (fun h' => h (congrFun h' 0))]

theorem Hsq_mono : Hop p ^ 2 = (lambdaP p ^ 2)⁻¹ • mono p (fun t => fun _ => -(t 0)) fun _ => 1 := by
  rw [sq, Hop_sq, Pneg_mono]

theorem Sop_pow_mono (hp2 : p ≠ 2) (k : ℕ) :
    Sop p ^ k = mono p id fun t => ψ p (k * q p (z p (t 0))) := by
  rw [Sop_mono p hp2, mono_id_pow]
  exact mono_ext p (fun _ => rfl) (fun t => ψ_pow p _ k)

theorem q_neg_sub (hp2 : p ≠ 2) (a : ZMod p) : q p (-a) - q p a = a := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  simp only [q]; field_simp; ring

theorem lambda_inv_four (hp2 : p ≠ 2) : (lambdaP p ^ 2)⁻¹ * (lambdaP p ^ 2)⁻¹ = 1 := by
  rw [← mul_inv, ← pow_add, lambdaP_pow_four p hp2, inv_one]

/-- Lemma A.15: the circuit (T3) is `Z |j⟩ = ω^j |j⟩`. -/
theorem sem_Z (hp2 : p ≠ 2) :
    ((sem p 1 (Z p) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      mono p id fun t => ψ p (z p (t 0)) := by
  simp only [Z, seq_def, map_mul, map_pow, Submonoid.coe_mul, SubmonoidClass.coe_pow, sem_H,
    sem_S]
  rw [Hsq_mono, Sop_pow_mono p hp2, Sop_mono p hp2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mono_mul, lambda_inv_four p hp2, one_smul]
  apply mono_ext p
  · intro t; funext i; rw [Subsingleton.elim i 0]; simp
  · intro t
    simp only [Function.comp_apply, id, one_mul, z_neg, natCast_pred]
    rw [← ψ_add]; congr 1
    linear_combination q_neg_sub p hp2 (z p (t 0))

omit hp in
theorem mono_mul_apply_invol {n : ℕ} (σ : State p n → State p n) (hσ : ∀ x, σ (σ x) = x)
    (φ : State p n → ℂ) (M : Op ℂ p n) (s t : State p n) :
    (mono p σ φ * M) s t = φ (σ s) * M (σ s) t := by
  rw [mul_apply, Finset.sum_eq_single (σ s)]
  · simp [mono, hσ]
  · intro u _ hu
    have : s ≠ σ u := fun h => hu (by rw [h, hσ])
    simp [mono, this]
  · simp

/-- Lemma A.16: the circuit (T2) is `X |j⟩ = |j + 1⟩`. -/
theorem sem_X (hp2 : p ≠ 2) :
    ((sem p 1 (X p) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      mono p (fun t => fun _ => t 0 + 1) fun _ => 1 := by
  simp only [X, seq_def, map_mul, map_pow, Submonoid.coe_mul, SubmonoidClass.coe_pow, sem_H,
    sem_S]
  rw [Hsq_mono, Sop_pow_mono p hp2, Sop_mono p hp2]
  simp only [smul_mul_assoc, mul_smul_comm]
  have hmid : (mono (n := 1) p id fun t => ψ p (q p (z p (t 0)))) * ((mono (n := 1) p (fun t => fun _ => -(t 0))
      fun _ => 1) * (mono (n := 1) p id fun t => ψ p (((p - 1 : ℕ) : ZMod p) * q p (z p (t 0))))) =
      mono (n := 1) p (fun t => fun _ => -(t 0)) fun t => ψ p (z p (t 0)) := by
    rw [mono_mul, mono_mul]
    apply mono_ext p
    · intro t; rfl
    · intro t
      simp only [Function.comp_apply, id, one_mul, z_neg, natCast_pred]
      rw [← ψ_add]; congr 1
      linear_combination q_neg_sub p hp2 (z p (t 0))
  have e : ∀ A B C D E : Op ℂ p 1, A * (B * (C * (D * E))) = A * ((B * (C * D)) * E) := by
    intros; simp only [mul_assoc]
  rw [e, hmid]
  ext l j
  rw [smul_apply, smul_eq_mul, mul_apply, sum_state1]
  have key : ∀ v : Fin p, Hop p l (fun _ => v) * (mono (n := 1) p (fun t => fun _ => -(t 0))
      (fun t => ψ p (z p (t 0))) * Hop p) (fun _ => v) j =
      hc p ^ 2 * ψ p ((z p (l 0) - 1 - z p (j 0)) * z p v) := by
    intro v
    rw [mono_mul_apply_invol p (fun t : State p 1 => fun _ => -(t 0))
      (fun x => by funext i; rw [Subsingleton.elim i 0]; simp), Hop_apply, Hop_apply]
    dsimp only
    simp only [z_neg]
    have : ∀ a b c : ZMod p, hc p * ψ p a * (ψ p b * (hc p * ψ p c)) =
        hc p ^ 2 * ψ p (a + b + c) := by
      intro a b c; rw [ψ_add, ψ_add]; ring
    rw [this]; congr 1; ring
  simp_rw [key, ← Finset.mul_sum]
  rw [sum_ψ, mono]
  have hz1 : z p (1 : Fin p) = 1 := by
    rw [z, Fin.val_one', ZMod.natCast_mod, Nat.cast_one]
  have hst : l = (fun _ => j 0 + 1) ↔ z p (l 0) - 1 - z p (j 0) = 0 := by
    constructor
    · rintro rfl; simp [z_add, hz1]
    · intro h
      apply state_one_ext p
      exact z_injective p (by rw [z_add, hz1]; linear_combination h)
  by_cases h : z p (l 0) - 1 - z p (j 0) = 0
  · rw [if_pos h, if_pos (hst.2 h), ← mul_assoc, cx_const p hp2]
  · rw [if_neg h, if_neg (fun h' => h (hst.1 h')), mul_zero, mul_zero]

/-! ### The multiplier -/

theorem two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)

/-- The quadratic Gauss sum `G(α) = ∑_n ψ(α n²)`. -/
def G (α : ZMod p) : ℂ := ∑ n : Fin p, ψ p (α * z p n ^ 2)

theorem sum_shift (f : ZMod p → ℂ) (γ : ZMod p) :
    ∑ n : Fin p, f (z p n + γ) = ∑ n : Fin p, f (z p n) := by
  exact Fintype.sum_equiv (Equiv.addRight (zinv p γ)) _ _
    (fun n => by simp only [Equiv.coe_addRight, z_add, z_zinv])

/-- Completing the square. -/
theorem sum_quad (hp2 : p ≠ 2) (α β : ZMod p) (hα : α ≠ 0) :
    ∑ n : Fin p, ψ p (α * z p n ^ 2 + β * z p n) = ψ p (-(β ^ 2 / (4 * α))) * G p α := by
  have h2 := two_ne_zero' p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have key : ∀ n : Fin p, α * z p n ^ 2 + β * z p n =
      α * (z p n + β / (2 * α)) ^ 2 + -(β ^ 2 / (4 * α)) := by
    intro n; field_simp; ring
  simp_rw [key, ψ_add, ← Finset.sum_mul]
  rw [mul_comm, G]
  congr 1
  exact sum_shift p (fun y => ψ p (α * y ^ 2)) _

omit hp in
theorem mono_id_mul_apply {n : ℕ} (d : State p n → ℂ) (M : Op ℂ p n) (s t : State p n) :
    (mono p id d * M) s t = d s * M s t :=
  mono_mul_apply_invol p id (fun _ => rfl) d M s t

/-- The core `H S^{a⁻¹} H S^a H S^{a⁻¹}` of (T1), in operator order. -/
theorem core_apply (hp2 : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) (w x : State p 1) :
    (Sop p ^ (a⁻¹).val * (Hop p * (Sop p ^ a.val * (Hop p * (Sop p ^ (a⁻¹).val * Hop p))))) w x =
      if z p (w 0) - a * z p (x 0) - (a - 1) / 2 = 0 then
        hc p ^ 3 * p * G p (a⁻¹ / 2) *
          ψ p (a⁻¹ * q p (z p (w 0)) - a * (z p (x 0) - a⁻¹ / 2) ^ 2 / 2)
      else 0 := by
  have h2 := two_ne_zero' p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hc2 : a⁻¹ / 2 ≠ 0 := div_ne_zero (inv_ne_zero ha) h2
  rw [Sop_pow_mono p hp2, Sop_pow_mono p hp2]
  simp only [ZMod.natCast_zmod_val]
  rw [mono_id_mul_apply, mul_apply, sum_state1]
  have hn : ∀ m n : Fin p, Hop p (fun _ => m) (fun _ => n) *
      (mono (n := 1) p id (fun t => ψ p (a⁻¹ * q p (z p (t 0)))) * Hop p) (fun _ => n) x =
      hc p ^ 2 * ψ p (a⁻¹ / 2 * z p n ^ 2 + (z p m + z p (x 0) - a⁻¹ / 2) * z p n) := by
    intro m n
    rw [mono_id_mul_apply, Hop_apply, Hop_apply]
    dsimp only
    have : ∀ u v y : ZMod p, hc p * ψ p u * (ψ p v * (hc p * ψ p y)) = hc p ^ 2 * ψ p (u + v + y) := by
      intro u v y; rw [ψ_add, ψ_add]; ring
    rw [this]; congr 1; simp only [q]; field_simp; ring
  have hm : ∀ m : Fin p, Hop p w (fun _ => m) *
      (mono (n := 1) p id (fun t => ψ p (a * q p (z p (t 0)))) *
        (Hop p * (mono (n := 1) p id (fun t => ψ p (a⁻¹ * q p (z p (t 0)))) * Hop p)) :
          Op ℂ p 1) (fun _ => m) x =
      hc p ^ 3 * G p (a⁻¹ / 2) * ψ p (-(a * (z p (x 0) - a⁻¹ / 2) ^ 2 / 2)) *
        ψ p ((z p (w 0) - a * z p (x 0) - (a - 1) / 2) * z p m) := by
    intro m
    rw [mono_id_mul_apply, mul_apply, sum_state1]
    simp_rw [hn, ← Finset.mul_sum]
    rw [sum_quad p hp2 _ _ hc2, Hop_apply]
    have : ∀ u v y : ZMod p, hc p * ψ p u * (ψ p v * (hc p ^ 2 * (ψ p y * G p (a⁻¹ / 2)))) =
        hc p ^ 3 * G p (a⁻¹ / 2) * ψ p (u + v + y) := by
      intro u v y; rw [ψ_add, ψ_add]; ring
    rw [this, mul_assoc (hc p ^ 3 * G p (a⁻¹ / 2)), ← ψ_add]
    congr 2; simp only [q]; field_simp; ring
  simp_rw [hm, ← Finset.mul_sum]
  rw [sum_ψ]
  split_ifs with h
  · rw [show a⁻¹ * q p (z p (w 0)) - a * (z p (x 0) - a⁻¹ / 2) ^ 2 / 2 =
      a⁻¹ * q p (z p (w 0)) + -(a * (z p (x 0) - a⁻¹ / 2) ^ 2 / 2) by ring, ψ_add]
    ring
  · ring

theorem sem1_scalar (k : ℕ) :
    ((sem p 1 (negω ^ k) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      mono p id fun _ => (-ωℂ p) ^ k := by
  rw [sem_scalar_pow, one_eq_mono, smul_mono]; simp

omit hp in
theorem mono_mul_apply_sum {n : ℕ} (σ : State p n → State p n) (φ : State p n → ℂ)
    (M : Op ℂ p n) (s t : State p n) :
    (mono p σ φ * M) s t = ∑ w, if s = σ w then φ w * M w t else 0 := by
  rw [mul_apply]; refine Finset.sum_congr rfl fun w _ => ?_
  simp only [mono]; split_ifs <;> simp

theorem xshift_iterate (k : ℕ) (t : State p 1) :
    z p ((fun t : State p 1 => fun _ : Fin 1 => t 0 + 1)^[k] t 0) = z p (t 0) + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', z_add, ih]
    have hz1 : z p (1 : Fin p) = 1 := by rw [z, Fin.val_one', ZMod.natCast_mod, Nat.cast_one]
    rw [hz1]; push_cast; ring

/-- The multiplier `|x⟩ ↦ |ax⟩`. -/
def multσ (a : ZMod p) (t : State p 1) : State p 1 := fun _ => zinv p (a * z p (t 0))

/-- The scalar of (T1): `M_a = κ_a P_a`. -/
def κM (a : ZMod p) : ℂ :=
  (-ωℂ p) ^ ((p + 1) * ((-a ^ 2 + 4 * a - 2) / (8 * a)).val) * (-ωℂ p) ^ (p * legendreExp p a) *
    (hc p ^ 3 * p * G p (a⁻¹ / 2) * ψ p (a⁻¹ * q p (-((1 - a) / 2)) - a * (a⁻¹ / 2) ^ 2 / 2))

/-- Lemma 2.15 up to its scalar: the circuit (T1) is `κ_a` times the
multiplier `|x⟩ ↦ |ax⟩`. -/
theorem sem_M (hp2 : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) :
    ((sem p 1 (M p a) : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) =
      κM p a • mono p (multσ p a) fun _ => 1 := by
  have h2 := two_ne_zero' p hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [M, ω, neg1, ← pow_mul, ← pow_mul]
  simp only [seq_def, map_mul, Submonoid.coe_mul]
  rw [sem1_scalar, sem1_scalar]
  simp only [map_pow, SubmonoidClass.coe_pow]
  rw [sem_Z p hp2, sem_X p hp2, sem_H, sem_S, mono_id_pow, mono_one_pow]
  ext y x
  rw [mono_id_mul_apply, mono_id_mul_apply, mono_id_mul_apply, mono_mul_apply_sum, sum_state1]
  have hcond : ∀ x1 : Fin p, (y = (fun t : State p 1 => fun _ : Fin 1 => t 0 + 1)^[((1 - a) / 2).val]
      fun _ => x1) ↔ z p x1 = z p (y 0) - (1 - a) / 2 := by
    intro x1
    constructor
    · rintro rfl; rw [xshift_iterate, ZMod.natCast_zmod_val]; ring
    · intro h
      apply state_one_ext p
      apply z_injective p
      rw [xshift_iterate, ZMod.natCast_zmod_val, h]; ring
  simp_rw [hcond, one_mul]
  rw [sum_ite_z, core_apply p hp2 a ha, smul_apply, smul_eq_mul, mono, z_zinv]
  have hy : y = multσ p a x ↔ z p (y 0) - (1 - a) / 2 - a * z p (x 0) - (a - 1) / 2 = 0 := by
    constructor
    · rintro rfl; simp only [multσ, z_zinv]; ring
    · intro h
      apply state_one_ext p
      apply z_injective p
      simp only [multσ, z_zinv]
      linear_combination h
  by_cases h : z p (y 0) - (1 - a) / 2 - a * z p (x 0) - (a - 1) / 2 = 0
  · rw [if_pos h, if_pos (hy.2 h), mul_one, κM, ψ_pow, ZMod.natCast_zmod_val]
    have hya : z p (y 0) = a * z p (x 0) := by linear_combination h
    rw [hya]
    have e : a⁻¹ * q p (-((1 - a) / 2)) - a * (a⁻¹ / 2) ^ 2 / 2 =
        (1 - a) / (2 * a) * (a * z p (x 0)) +
          (a⁻¹ * q p (a * z p (x 0) - (1 - a) / 2) - a * (z p (x 0) - a⁻¹ / 2) ^ 2 / 2) := by
      simp only [q]; field_simp; ring
    rw [e, ψ_add]; ring
  · rw [if_neg h, if_neg (fun h' => h (hy.1 h'))]; simp


/-! ### (C4) and (C9) -/

/-- (C4) `S ⨾ M_g = M_g ⨾ S^{g⁻²} ⨾ Z^{(1-g)/(2g²)}`, for any `g ≠ 0`. -/
theorem sound_C4 (hp2 : p ≠ 2) (g : ZMod p) (hg : g ≠ 0) :
    sem p 1 (S ⨾ M p g) =
      sem p 1 (M p g ⨾ S ^ ((g ^ 2)⁻¹).val ⨾ Z p ^ ((1 - g) / (2 * g ^ 2)).val) := by
  have h2 := two_ne_zero' p hp2
  apply Subtype.ext
  simp only [seq_def, map_mul, Submonoid.coe_mul, map_pow, SubmonoidClass.coe_pow]
  rw [sem_M p hp2 g hg, sem_S, sem_Z p hp2, Sop_pow_mono p hp2, Sop_mono p hp2, mono_id_pow,
    smul_mul_assoc, mul_smul_comm, mul_smul_comm, mono_mul, mono_mul, mono_mul]
  congr 1
  apply mono_ext p
  · intro t; rfl
  · intro t
    simp only [Function.comp_apply, id, one_mul, multσ, z_zinv, ψ_pow, ZMod.natCast_zmod_val]
    rw [mul_one, ← ψ_add]
    congr 1
    simp only [q]; field_simp; ring

omit hp in
theorem split11_symm (a b : State p 1) : (split p 1 1).symm (a, b) = ![a 0, b 0] := by
  funext i; fin_cases i <;> rfl

omit hp in
theorem onTop_mono2 (σ : State p 1 → State p 1) (φ : State p 1 → ℂ) :
    onTop 1 (mono p σ φ) = mono p (fun t : State p 2 => ![t 0, σ (fun _ => t 1) 0])
      fun t => φ fun _ => t 1 := by
  rw [onTop_mono]
  have h1 : ∀ t : State p 2, (split p 1 1 t).1 = fun _ => t 0 := by
    intro t; funext i; rw [Subsingleton.elim i 0]; rfl
  have h2 : ∀ t : State p 2, (split p 1 1 t).2 = fun _ => t 1 := by
    intro t; funext i; rw [Subsingleton.elim i 0]; rfl
  apply mono_ext p
  · intro t; rw [split11_symm, h1, h2]
  · intro t; rw [h2]

/-- (C9) `M_g` on the top wire, then `CZ`, is `CZ^g`, then `M_g` on the top
wire, for any `g ≠ 0`. -/
theorem sound_C9 (hp2 : p ≠ 2) (g : ZMod p) (hg : g ≠ 0) :
    sem p 2 (top (M p g) ⨾ CZ) = sem p 2 (CZ ^ g.val ⨾ top (M p g)) := by
  apply Subtype.ext
  simp only [seq_def, map_mul, Submonoid.coe_mul, map_pow, SubmonoidClass.coe_pow]
  rw [sem_top, sem_M p hp2 g hg, sem_CZ, onTop_smul, CZop_mono, mono_id_pow, onTop_mono2,
    smul_mul_assoc, mul_smul_comm, mono_mul, mono_mul]
  congr 1
  apply mono_ext p
  · intro t; rfl
  · intro t
    simp only [one_mul, mul_one, multσ, z_zinv, ψ_pow, ZMod.natCast_zmod_val, cons2_zero,
      cons2_one]
    congr 1; ring

end

end QCert.QuditClifford
