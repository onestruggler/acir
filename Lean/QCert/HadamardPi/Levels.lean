/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# How one generator changes the level

* A generator acting below the pivot does not raise the level when it
  permutes or negates entries (`X`, `(-1)`).
* `X_[p,q]` with `q` at or above the pivot makes column `q` equal to `e_p`:
  the level becomes `(q+1, 0, 0)`; `(-1)_[p]` with `p` at or above the
  pivot gives `(p+1, 0, 0)`; `H_[p,q]` with `q` at or above the pivot
  gives `(q+1, 1, 2)`.

Hence `lev (X_[p,q] t) ≤ max (lev t) (q+1, 0, 0)` and
`lev ((-1)_[p] t) ≤ max (lev t) (p+1, 0, 0)` in all cases.
-/
import QCert.HadamardPi.Synth
import Mathlib.NumberTheory.Real.Irrational

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

/-- The level `(q+1, 0, 0)`. -/
def lev0 (q : ℕ) : ℕ ×ₗ (ℕ ×ₗ ℕ) := toLex (q + 1, toLex (0, 0))

theorem piv_eq {M : O n} {q : Fin n} (hq : ¬Fixed M q) (h : ∀ j : Fin n, q < j → Fixed M j) :
    piv M = q + 1 :=
  le_antisymm (piv_le fun j hj => h j (by rw [Fin.lt_def]; omega))
    (by by_contra hlt; exact hq (fixed_of_piv_le (by omega)))

theorem lev_eq_of {M : O n} {q : Fin n} (hq : ¬Fixed M q) (h : ∀ j : Fin n, q < j → Fixed M j) :
    lev M = toLex ((q : ℕ) + 1, kl (col M q)) := by
  have hp := piv_eq hq h
  have hp0 : 0 < piv M := by omega
  have hpj : pj M hp0 = q := Fin.ext (by simp only [pj]; omega)
  rw [lev, pcol_eq hp0, hpj, hp]

theorem lde_eq_zero_of_int {v : Fin n → ℝ} (h : ∀ i, ∃ z : ℤ, v i = z) : lde v = 0 :=
  Nat.eq_zero_of_le_zero (lde_le fun i => by
    obtain ⟨z, hz⟩ := h i; rw [hz]; exact den_intCast 0 z)

theorem kl_single (p : Fin n) (ε : ℤ) : kl (Pi.single p (ε : ℝ)) = toLex (0, 0) := by
  have : lde (Pi.single p (ε : ℝ)) = 0 := lde_eq_zero_of_int fun i => by
    by_cases h : i = p
    · subst h; exact ⟨ε, by simp⟩
    · exact ⟨0, by simp [h]⟩
  simp [kl, this]

theorem lev0_le {M : O n} {q : ℕ} (hq : q < piv M) : lev0 q ≤ lev M := by
  rw [lev0, lev]
  rcases Nat.lt_or_ge (q + 1) (piv M) with h | h
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.2 (Or.inl h))
  · have : q + 1 = piv M := by omega
    rw [this]
    apply Prod.Lex.toLex_le_toLex.2
    right; refine ⟨rfl, ?_⟩
    apply Prod.Lex.toLex_le_toLex.2
    rcases Nat.eq_zero_or_pos (ofLex (kl (pcol M))).1 with h0 | h0
    · right; refine ⟨h0.symm, Nat.zero_le _⟩
    · left; exact h0

/-! ### Signed permutations below the pivot -/

theorem kl_xv {v : Fin n → ℝ} (hR : InRing v) (p q : Fin n) : kl (xv p q v) = kl v := by
  simp only [kl, lde_xv p q hR, card_oddSet_xv hR]

theorem card_oddSet_zv {v : Fin n → ℝ} (hR : InRing v) (p : Fin n) :
    (oddSet (zv p v)).card = (oddSet v).card := by
  congr 1
  ext i
  simp only [mem_oddSet, num_zv p hR]
  split_ifs <;> simp [odd_neg]

theorem kl_zv {v : Fin n → ℝ} (hR : InRing v) (p : Fin n) : kl (zv p v) = kl v := by
  simp only [kl, lde_zv p hR, card_oddSet_zv hR]

/-- A generator that permutes or negates entries does not raise the level
when it acts below the pivot. -/
theorem lev_perm_le {t : O n} {g : Gen n} (hg : ∀ v : Fin n → ℝ, InRing v → kl (gv g v) = kl v)
    (hb : ∀ i ∈ g.idx, (i : ℕ) < piv t) : lev (sem n g * t) ≤ lev t := by
  have hB : Below (piv t) (FreeMonoid.of g) := Below.of hb
  have hle := piv_le_of_below hB
  simp only [FreeMonoid.lift_eval_of] at hle
  rcases lt_or_eq_of_le hle with h | h
  · exact le_of_lt (lev_lt_iff.2 (Or.inl h))
  · have hp : 0 < piv t := by
      obtain ⟨i, hi⟩ : ∃ i, i ∈ g.idx := by cases g <;> simp [Gen.idx]
      have := hb i hi; omega
    have hpc := pcol_of_piv_eq (w := FreeMonoid.of g) (by simpa using h) hp
    simp only [FreeMonoid.lift_eval_of, wv_of] at hpc
    rw [lev, lev, h, hpc, hg _ (col_inRing t _), ← pcol_eq hp]

theorem lev_X_le {t : O n} {p q : Fin n} (hpq : p < q) (hq : (q : ℕ) < piv t) :
    lev (sem n (Gen.X p q hpq) * t) ≤ lev t :=
  lev_perm_le (fun v hR => kl_xv hR p q) fun i hi => by
    simp [Gen.idx] at hi; rcases hi with rfl | rfl
    · rw [Fin.lt_def] at hpq; omega
    · exact hq

theorem lev_Z_le {t : O n} {p : Fin n} (hp : (p : ℕ) < piv t) :
    lev (sem n (Gen.Z p) * t) ≤ lev t :=
  lev_perm_le (fun v hR => kl_zv hR p) fun i hi => by simp [Gen.idx] at hi; subst hi; exact hp

/-! ### Generators above the pivot -/

theorem fixed_of_lt {t : O n} {j : Fin n} (h : piv t ≤ j) : col t j = Pi.single j 1 :=
  fixed_of_piv_le h

/-- `X_[p,q]` at or above the pivot: the level becomes `(q+1, 0, 0)`. -/
theorem lev_X_of_le {t : O n} {p q : Fin n} (hpq : p < q) (hq : piv t ≤ q) :
    lev (sem n (Gen.X p q hpq) * t) = lev0 q := by
  have hcol : ∀ j, col (sem n (Gen.X p q hpq) * t) j = xv p q (col t j) :=
    fun j => col_sem_mul _ _ _
  have hcq : col (sem n (Gen.X p q hpq) * t) q = Pi.single p 1 := by
    rw [hcol, fixed_of_lt hq]
    funext i; simp only [xv]
    split_ifs with h1 h2
    · subst h1; simp
    · subst h2; simp [Pi.single_apply, ne_of_gt hpq]
    · simp [Pi.single_apply, h1, h2]
  have hnf : ¬Fixed (sem n (Gen.X p q hpq) * t) q := by
    intro h
    have := congrFun (hcq.symm.trans h) p
    simp [Pi.single_apply, ne_of_lt hpq] at this
  rw [lev_eq_of hnf (fun j hj => ?_), hcq, show ((1 : ℝ)) = ((1 : ℤ) : ℝ) by simp, kl_single,
    lev0]
  show col _ j = _
  rw [hcol, fixed_of_lt (by rw [Fin.lt_def] at hj; omega)]
  exact gv_single (g := Gen.X p q hpq) (by
    simp only [Gen.idx, mem_insert, mem_singleton, not_or]
    exact ⟨(hpq.trans hj).ne', hj.ne'⟩)

/-- `(-1)_[p]` at or above the pivot: the level becomes `(p+1, 0, 0)`. -/
theorem lev_Z_of_le {t : O n} {p : Fin n} (hp : piv t ≤ p) :
    lev (sem n (Gen.Z p) * t) = lev0 p := by
  have hcol : ∀ j, col (sem n (Gen.Z p) * t) j = zv p (col t j) := fun j => col_sem_mul _ _ _
  have hcp : col (sem n (Gen.Z p) * t) p = Pi.single p ((-1 : ℤ) : ℝ) := by
    rw [hcol, fixed_of_lt hp]
    funext i; simp only [zv]
    split_ifs with h1
    · subst h1; simp
    · simp [Pi.single_apply, h1]
  have hnf : ¬Fixed (sem n (Gen.Z p) * t) p := by
    intro h
    have := congrFun (hcp.symm.trans h) p
    norm_num at this
  rw [lev_eq_of hnf (fun j hj => ?_), hcp, kl_single, lev0]
  show col _ j = _
  rw [hcol, fixed_of_lt (by rw [Fin.lt_def] at hj; omega)]
  exact gv_single (g := Gen.Z p) (by
    simp only [Gen.idx, mem_singleton]; intro h; subst h; exact lt_irrefl _ hj)

theorem lev_X_le_max {t : O n} {p q : Fin n} (hpq : p < q) :
    lev (sem n (Gen.X p q hpq) * t) ≤ max (lev t) (lev0 q) := by
  rcases Nat.lt_or_ge (q : ℕ) (piv t) with h | h
  · exact le_max_of_le_left (lev_X_le hpq h)
  · rw [lev_X_of_le hpq h]; exact le_max_right _ _

theorem lev_Z_le_max {t : O n} {p : Fin n} :
    lev (sem n (Gen.Z p) * t) ≤ max (lev t) (lev0 p) := by
  rcases Nat.lt_or_ge (p : ℕ) (piv t) with h | h
  · exact le_max_of_le_left (lev_Z_le h)
  · rw [lev_Z_of_le h]; exact le_max_right _ _

/-! ### `H` above the pivot -/

theorem not_den_zero_invSqrt2 : ¬Den 0 invSqrt2 := by
  rintro ⟨u, hu⟩
  rw [toReal_apply, pow_zero, one_mul] at hu
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 := sqrt2_ne_zero
  have key : (u.re : ℝ) * Real.sqrt 2 + 2 * u.im = 1 := by
    have := congrArg (· * Real.sqrt 2) hu
    simp only [invSqrt2] at this
    rw [inv_mul_cancel₀ h0] at this
    linear_combination this - u.im * h2
  by_cases hre : u.re = 0
  · rw [hre] at key; push_cast at key
    have : (2 * u.im : ℤ) = 1 := by exact_mod_cast (by linarith : (2 * (u.im : ℝ)) = 1)
    omega
  · apply irrational_sqrt_two
    refine ⟨((1 - 2 * u.im : ℤ) : ℚ) / u.re, ?_⟩
    have : (u.re : ℝ) ≠ 0 := by exact_mod_cast hre
    push_cast
    field_simp
    linarith

/-- The column `(e_p - e_q)/√2`. -/
theorem hv_single_facts {p q : Fin n} (hpq : p ≠ q) :
    InRing (hv p q (Pi.single q 1)) ∧ lde (hv p q (Pi.single q 1)) = 1 ∧
      num (hv p q (Pi.single q 1)) = (fun i => if i = p then 1 else if i = q then -1 else 0) ∧
      oddSet (hv p q (Pi.single q 1)) = {p, q} := by
  classical
  set v := hv p q (Pi.single q (1 : ℝ))
  have hvp : v p = invSqrt2 := by simp [v, hv, hpq]
  have hvq : v q = -invSqrt2 := by simp [v, hv, hpq, Ne.symm hpq]
  have hvo : ∀ i, i ≠ p → i ≠ q → v i = 0 := fun i h1 h2 => by simp [v, hv, h1, h2]
  set u : Fin n → ℤ√2 := fun i => if i = p then 1 else if i = q then -1 else 0
  have hu : ∀ i, toReal (u i) = Real.sqrt 2 ^ 1 * v i := by
    intro i
    by_cases h1 : i = p
    · subst h1; simp [u, hvp, sqrt2_mul_invSqrt2]
    · by_cases h2 : i = q
      · subst h2; simp [u, h1, hvq, sqrt2_mul_invSqrt2]
      · simp [u, h1, h2, hvo i h1 h2]
  have hR : InRing v := fun i => by
    by_cases h1 : i = p
    · subst h1; rw [hvp]; exact invSqrt2_mem
    · by_cases h2 : i = q
      · subst h2; rw [hvq]; exact ZInvSqrt2.neg_mem invSqrt2_mem
      · rw [hvo i h1 h2]; exact ZInvSqrt2.zero_mem
  have hl : lde v = 1 := by
    apply le_antisymm (lde_le fun i => ⟨u i, hu i⟩)
    by_contra h0
    have h00 : lde v = 0 := by omega
    have := denV_lde hR p
    rw [h00, hvp] at this
    exact not_den_zero_invSqrt2 this
  have hnum : num v = u := num_eq hR (by rw [hl]; exact hu)
  have hodd : oddSet v = {p, q} := by
    ext i
    rw [mem_oddSet, hnum]
    by_cases h1 : i = p
    · subst h1; simp [u]
    · by_cases h2 : i = q
      · subst h2; simp [u, h1]
      · simp [u, h1, h2]
  exact ⟨hR, hl, hnum, hodd⟩

theorem kl_hv_single {p q : Fin n} (hpq : p ≠ q) :
    kl (hv p q (Pi.single q 1)) = toLex (1, 2) := by
  obtain ⟨_, hl, _, hodd⟩ := hv_single_facts hpq
  simp [kl, hl, hodd, card_pair hpq]

/-- `H_[p,q]` at or above the pivot: the level becomes `(q+1, 1, 2)`. -/
theorem lev_H_of_le {t : O n} {p q : Fin n} (hpq : p < q) (hq : piv t ≤ q) :
    lev (sem n (Gen.H p q hpq) * t) = toLex ((q : ℕ) + 1, toLex (1, 2)) := by
  have hcol : ∀ j, col (sem n (Gen.H p q hpq) * t) j = hv p q (col t j) :=
    fun j => col_sem_mul _ _ _
  have hcq : col (sem n (Gen.H p q hpq) * t) q = hv p q (Pi.single q 1) := by
    rw [hcol, fixed_of_lt hq]
  have hnf : ¬Fixed (sem n (Gen.H p q hpq) * t) q := by
    intro h
    have := congrFun (hcq.symm.trans h) p
    simp [hv, ne_of_lt hpq, invSqrt2] at this
  rw [lev_eq_of hnf (fun j hj => ?_), hcq, kl_hv_single (ne_of_lt hpq)]
  show col _ j = _
  rw [hcol, fixed_of_lt (by rw [Fin.lt_def] at hj; omega)]
  exact gv_single (g := Gen.H p q hpq) (by
    simp only [Gen.idx, mem_insert, mem_singleton, not_or]
    exact ⟨(hpq.trans hj).ne', hj.ne'⟩)

end QCert.HadamardPi
