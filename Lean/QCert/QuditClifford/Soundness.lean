/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qudit Clifford circuits: soundness

Each rule of Figure 1 is sound for the matrices of Definition 2.11, at
every odd prime `p` (Proposition A.28, by the path-sum calculations of
Lemmas A.25–A.27).  Proved here: the rules whose
circuits are diagonal, (C0), (C1), (C6) and (C8), and (C5), from
Proposition 2.13 (`H² = λ_p⁻² M_{-1}`, `Hop_sq`); the others are in
`QuditClifford.Theorem` (`rule_sound`), with `sorry`s that `README.md`
lists.
-/
import QCert.QuditClifford.Semantics

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Diagonal operators -/

omit hp in
theorem onBottom_zero_one (A : Op ℂ p 1) : onBottom (n := 0) A = A := by
  ext s t; rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

omit hp in
theorem onBottom_zero_two (A : Op ℂ p 2) : onBottom (n := 0) A = A := by
  ext s t; rw [onBottom_apply', if_pos (fun i hi hk => by omega)]

omit hp in
theorem onTop_diagonal {n k : ℕ} (d : State p n → ℂ) :
    onTop k (Matrix.diagonal d) = Matrix.diagonal fun s => d (split p n k s).2 := by
  ext s t
  rw [onTop_apply, diagonal_apply, diagonal_apply]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd ((split p n k).injective (Prod.ext h1 h2)) h
    · rfl
    · rfl

theorem sem_S : ((sem p 1 S : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) = Sop p := by
  show onBottom (n := 0) (Sop p) = Sop p
  exact onBottom_zero_one p _

theorem sem_CZ : ((sem p 2 CZ : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = CZop p := by
  show onBottom (n := 0) (CZop p) = CZop p
  exact onBottom_zero_two p _

theorem sem_negω {n : ℕ} :
    ((sem p n negω : unitaryGroup (State p n) ℂ) : Op ℂ p n) = Matrix.diagonal fun _ => -ωℂ p := by
  show (-ωℂ p) • (1 : Op ℂ p n) = _
  ext s t; by_cases h : s = t <;> simp [h]

theorem diagonal_pow_eq_one {m : Type} [Fintype m] [DecidableEq m] (e : m → ℕ) :
    (Matrix.diagonal fun s => ωℂ p ^ e s) ^ p = 1 := by
  rw [diagonal_pow, ← diagonal_one]
  congr 1; funext s
  rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, ωℂ_pow_p, one_pow]

/-! ### The diagonal rules -/

/-- (C0) `(-ω)^{2p} = 1`. -/
theorem sound_C0 : sem p 0 (negω ^ (2 * p)) = sem p 0 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_negω, map_one, Submonoid.coe_one, diagonal_pow,
    ← diagonal_one]
  congr 1; funext s
  rw [Pi.pow_apply, pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, ωℂ_pow_p, one_pow]

/-- (C1) `S^p = 1`. -/
theorem sound_C1 : sem p 1 (S ^ p) = sem p 1 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_S, map_one, Submonoid.coe_one]
  exact diagonal_pow_eq_one p _

/-- (C6) `CZ^p = 1`. -/
theorem sound_C6 : sem p 2 (CZ ^ p) = sem p 2 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_CZ, map_one, Submonoid.coe_one]
  exact diagonal_pow_eq_one p _

/-- (C8) `S` on the top wire commutes with `CZ`. -/
theorem sound_C8 : sem p 2 (top S ⨾ CZ) = sem p 2 (CZ ⨾ top S) := by
  apply Subtype.ext
  have hS : ((sem p 2 (top S) : unitaryGroup (State p 2) ℂ) : Op ℂ p 2) = onTop 1 (Sop p) := by
    have := (gateSem p).sem_shift (n := 1) S
    rw [this]; show onTop 1 _ = _; rw [sem_S]
  rw [seq_def, seq_def, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, hS, sem_CZ, Sop,
    onTop_diagonal, CZop, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext s; ring

/-! ### `H²` and (C5) -/

omit hp in
/-- `p ∣ a + b` exactly when `b = -a` in `ℤ_p`. -/
theorem dvd_add_iff_eq_neg (a b : Fin p) : p ∣ a.val + b.val ↔ b = -a := by
  have ha := a.isLt; have hb := b.isLt
  constructor
  · rintro ⟨k, hk⟩
    have hk2 : k < 2 := by
      by_contra h; push Not at h
      have : p * 2 ≤ p * k := Nat.mul_le_mul_left p h
      omega
    ext
    rw [Fin.val_neg']
    interval_cases k
    · have h0 : a.val = 0 := by omega
      have h1 : b.val = 0 := by omega
      rw [h0, h1, Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rintro rfl
    rw [Fin.val_neg']
    by_cases h0 : a.val = 0
    · rw [h0, Nat.sub_zero, Nat.mod_self]; exact dvd_zero p
    · rw [Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel' ha.le]

/-- `∑_u (ω^e)^u = p` if `p ∣ e`, and `0` otherwise. -/
theorem sum_pow_dvd (e : ℕ) :
    ∑ u : Fin p, (ωℂ p ^ e) ^ u.val = if p ∣ e then (p : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun u => (ωℂ p ^ e) ^ u)]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul, ωℂ_pow_p, one_pow]; simp
  · apply IsPrimitiveRoot.geom_sum_eq_zero _ hp.out.one_lt
    apply (ωℂ_primitive p).pow_of_coprime
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    exact h

/-- The multiplier by `-1` on one wire: `|j⟩ ↦ |-j⟩`. -/
def Pneg : Op ℂ p 1 := fun s t => if s 0 = -(t 0) then 1 else 0

omit hp in
theorem state_one_ext {s t : State p 1} (h : s 0 = t 0) : s = t :=
  funext fun i => by rw [Subsingleton.elim i 0, h]

/-- Proposition 2.13: `H² = λ_p⁻² M_{-1}`. -/
theorem Hop_sq : Hop p * Hop p = (lambdaP p ^ 2)⁻¹ • Pneg p := by
  ext s t
  rw [mul_apply, smul_apply, Pneg, smul_eq_mul]
  have hterm : ∀ u : State p 1, Hop p s u * Hop p u t =
      (lambdaP p * (Real.sqrt p : ℂ))⁻¹ ^ 2 * (ωℂ p ^ ((s 0).val + (t 0).val)) ^ (u 0).val := by
    intro u
    rw [Hop, Hop, ← pow_mul, show ((s 0).val + (t 0).val) * (u 0).val =
      (u 0).val * (s 0).val + (t 0).val * (u 0).val by ring, pow_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [show (∑ u : State p 1, (ωℂ p ^ ((s 0).val + (t 0).val)) ^ (u 0).val) =
      ∑ u : Fin p, (ωℂ p ^ ((s 0).val + (t 0).val)) ^ u.val from
    (Equiv.funUnique (Fin 1) (Fin p)).sum_comp
      (fun u : Fin p => (ωℂ p ^ ((s 0).val + (t 0).val)) ^ u.val),
    sum_pow_dvd]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hs : (Real.sqrt p : ℂ) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]; simp
  by_cases h1 : s 0 = -(t 0)
  · have h2 : p ∣ (s 0).val + (t 0).val :=
      (dvd_add_iff_eq_neg p _ _).2 (by rw [h1, neg_neg])
    rw [if_pos h2, if_pos h1, mul_one, inv_pow, mul_pow, hs, mul_inv, mul_assoc,
      inv_mul_cancel₀ hp0, mul_one]
  · have h2 : ¬ p ∣ (s 0).val + (t 0).val := fun h =>
      h1 (by rw [(dvd_add_iff_eq_neg p _ _).1 h, neg_neg])
    rw [if_neg h2, if_neg h1, mul_zero, mul_zero]

omit hp in
theorem Pneg_diagonal_Pneg (d : State p 1 → ℂ) :
    Pneg p * Matrix.diagonal d * Pneg p = Matrix.diagonal fun s => d (fun _ => -(s 0)) := by
  ext s t
  rw [mul_apply, diagonal_apply]
  simp_rw [mul_diagonal, Pneg]
  rw [Finset.sum_eq_single (fun _ => -(s 0))]
  · simp only [neg_neg, if_true, one_mul]
    by_cases h : s = t
    · subst h; simp
    · have h' : ¬ (-(s 0) = -(t 0)) := fun h' => h (state_one_ext p (neg_inj.mp h'))
      simp [h, h']
  · intro u _ hu
    rw [if_neg, zero_mul, zero_mul]
    intro h; exact hu (state_one_ext p (by show u 0 = -(s 0); rw [h, neg_neg]))
  · simp

theorem sem_H : ((sem p 1 H : unitaryGroup (State p 1) ℂ) : Op ℂ p 1) = Hop p := by
  show onBottom (n := 0) (Hop p) = Hop p
  exact onBottom_zero_one p _

/-- (C5) `H² ⨾ S ⨾ H² ⨾ S = S ⨾ H² ⨾ S ⨾ H²`: by Proposition 2.13 both sides
are `λ_p⁻⁴` times a product of two commuting diagonal matrices. -/
theorem sound_C5 : sem p 1 (H ^ 2 ⨾ S ⨾ H ^ 2 ⨾ S) = sem p 1 (S ⨾ H ^ 2 ⨾ S ⨾ H ^ 2) := by
  apply Subtype.ext
  simp only [seq_def, map_mul, map_pow, Submonoid.coe_mul, SubmonoidClass.coe_pow, sem_H, sem_S]
  rw [sq, Hop_sq]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  have key : Pneg p * Sop p * Pneg p =
      Matrix.diagonal fun s : State p 1 => ωℂ p ^ ((-(s 0)).val * ((-(s 0)).val - 1) / 2) := by
    rw [Sop]; exact Pneg_diagonal_Pneg p _
  calc Sop p * (Pneg p * (Sop p * Pneg p)) = Sop p * (Pneg p * Sop p * Pneg p) := by
        simp only [mul_assoc]
    _ = (Pneg p * Sop p * Pneg p) * Sop p := by
        rw [key, Sop, diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; funext s; ring
    _ = Pneg p * (Sop p * (Pneg p * Sop p)) := by simp only [mul_assoc]

end QCert.QuditClifford
