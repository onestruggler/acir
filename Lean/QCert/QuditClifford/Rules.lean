/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of the rules with swaps and `CX`

(C7), (C10)–(C12) on two qudits and (C13)–(C15) on three (Lemmas A.26,
A.27): with the swap and `CX` permutations (`sem_SWAP`, `sem_CX`) every
circuit in these rules except the `H` of (C11) is a monomial operator, and
the rules are equalities of permutations and phases.
-/
import QCert.QuditClifford.TwoQudit

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ### Monomial calculus -/

omit hp in
theorem mono_one_pow {n : ℕ} (σ : State p n → State p n) (k : ℕ) :
    mono p σ (fun _ => 1) ^ k = mono p (σ^[k]) fun _ => 1 := by
  induction k with
  | zero => rw [pow_zero, one_eq_mono]; rfl
  | succ k ih =>
    rw [pow_succ, ih, mono_mul]
    apply mono_ext p (fun t => (Function.iterate_succ_apply σ k t).symm) (fun t => by ring)

omit hp in
theorem mono_id_pow {n : ℕ} (φ : State p n → ℂ) (k : ℕ) :
    mono p id φ ^ k = mono p id fun t => φ t ^ k := by
  induction k with
  | zero => rw [pow_zero, one_eq_mono]; simp
  | succ k ih =>
    rw [pow_succ, ih, mono_mul]
    apply mono_ext p (fun t => rfl) (fun t => by simp [pow_succ])

omit hp in
theorem state2_ext {s t : State p 2} : s = t ↔ s 0 = t 0 ∧ s 1 = t 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; rw [state2_eq p s, state2_eq p t, h0, h1]

omit hp in
theorem onTop_diag2 (φ : State p 1 → ℂ) :
    onTop 1 (mono p id φ) = mono p id fun t : State p 2 => φ fun _ => t 1 := by
  ext s t
  rw [onTop_two]
  simp only [mono, id]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h]
    split_ifs with h0 h1
    · exact absurd ((state2_ext p).2 ⟨h0, congrFun h1 0⟩) h
    · rfl
    · rfl

omit hp in
theorem onBottom_diag2 (φ : State p 1 → ℂ) :
    onBottom (n := 1) (mono p id φ) = mono p id fun t : State p 2 => φ fun _ => t 0 := by
  ext s t
  rw [onBottom_two]
  simp only [mono, id]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h]
    split_ifs with h1 h0
    · exact absurd ((state2_ext p).2 ⟨congrFun h0 0, h1⟩) h
    · rfl
    · rfl

theorem ψ_pow (a : ZMod p) (k : ℕ) : ψ p a ^ k = ψ p (k * a) := by
  induction k with
  | zero => simp [ψ_zero]
  | succ k ih => rw [pow_succ, ih, ← ψ_add]; push_cast; ring_nf

theorem Sop_mono (hp2 : p ≠ 2) : Sop p = mono p id fun t => ψ p (q p (z p (t 0))) := by
  ext s t; rw [Sop_apply p hp2]; simp only [mono, id]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h, if_neg h]

theorem CZop_mono : CZop p = mono p id fun t => ψ p (z p (t 1) * z p (t 0)) := by
  ext s t; rw [CZop_apply]; simp only [mono, id]
  by_cases h : s = t
  · subst h; simp
  · rw [if_neg h, if_neg h]

theorem natCast_pred : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp.out.one_lt.le, ZMod.natCast_self]; simp

/-! ### Two-qudit rules -/

/-- (C7) `SWAP² = 1`. -/
theorem sound_C7 (hp2 : p ≠ 2) : sem p 2 (SWAP p ^ 2) = sem p 2 1 := by
  apply Subtype.ext
  rw [map_pow, SubmonoidClass.coe_pow, sem_SWAP p hp2, map_one, Submonoid.coe_one, sq, mono_mul,
    one_eq_mono]
  exact mono_ext p (fun t => swap2_swap2 p t) (fun t => by ring)

/-- The two sides of (C10) and (C11): a gate on the top wire, then the swap,
is the swap, then the gate on the bottom wire. -/
theorem sound_swap_gate (hp2 : p ≠ 2) (c : Circ 1) :
    sem p 2 (top c ⨾ SWAP p) = sem p 2 (SWAP p ⨾ bot c) := by
  apply Subtype.ext
  rw [seq_def, seq_def, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, sem_SWAP p hp2,
    sem_top, sem_bot]
  exact swap_onTop p _

/-- (C10). -/
theorem sound_C10 (hp2 : p ≠ 2) : sem p 2 (top S ⨾ SWAP p) = sem p 2 (SWAP p ⨾ bot S) :=
  sound_swap_gate p hp2 S

/-- (C11). -/
theorem sound_C11 (hp2 : p ≠ 2) : sem p 2 (top H ⨾ SWAP p) = sem p 2 (SWAP p ⨾ bot H) :=
  sound_swap_gate p hp2 H

theorem cx2_iterate (k : ℕ) (t : State p 2) :
    (cx2 p)^[k] t 1 = t 1 ∧ z p ((cx2 p)^[k] t 0) = z p (t 0) + k * z p (t 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1, ?_⟩
    show z p ((cx2 p)^[k] t 0 + (cx2 p)^[k] t 1) = _
    rw [z_add, ih.2, ih.1]; push_cast; ring

theorem cx2_inv (t : State p 2) : (cx2 p)^[p - 1] (cx2 p t) = t := by
  have h := cx2_iterate p (p - 1) (cx2 p t)
  rw [state2_ext]
  refine ⟨z_injective p ?_, h.1⟩
  rw [h.2, natCast_pred]
  show z p (t 0 + t 1) + -1 * z p (t 1) = z p (t 0)
  rw [z_add]; ring

theorem q_add (hp2 : p ≠ 2) (a b : ZMod p) : q p (a + b) - q p a - q p b = a * b := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  simp only [q]; field_simp; ring

/-- (C12) `CX ⨾ S₀ ⨾ CX^{-1} ⨾ S₁^{-1} ⨾ S₀^{-1} = CZ`: the phase
`q(j + ℓ) - q(j) - q(ℓ) = jℓ`, `q(j) = j(j - 1)/2`. -/
theorem sound_C12 (hp2 : p ≠ 2) :
    sem p 2 (CX ⨾ bot S ⨾ CX ^ (p - 1) ⨾ top (S ^ (p - 1)) ⨾ bot (S ^ (p - 1))) = sem p 2 CZ := by
  apply Subtype.ext
  simp only [seq_def]
  rw [map_mul, map_mul, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    Submonoid.coe_mul, sem_bot, sem_top, sem_bot]
  simp only [map_pow, SubmonoidClass.coe_pow]
  rw [sem_S, sem_CX p hp2, sem_CZ, Sop_mono p hp2, mono_id_pow, onBottom_diag2, onTop_diag2,
    onBottom_diag2, mono_one_pow, mono_mul, mono_mul, mono_mul, mono_mul, CZop_mono]
  apply mono_ext p
  · intro t; exact cx2_inv p t
  · intro t
    simp only [Function.comp_apply, id, cx2_inv]
    rw [ψ_pow, ψ_pow, natCast_pred]
    have hx : z p (cx2 p t 0) = z p (t 0) + z p (t 1) := z_add p _ _
    rw [hx]
    have : ∀ a b c : ZMod p, ψ p a * (ψ p b * (1 * (ψ p c * 1))) = ψ p (a + b + c) := by
      intro a b c; rw [ψ_add, ψ_add]; ring
    rw [this]
    congr 1
    linear_combination q_add p hp2 (z p (t 0)) (z p (t 1))

end

end QCert.QuditClifford
