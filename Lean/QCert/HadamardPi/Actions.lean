/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The generators acting on columns

`(-1)_[p]` negates entry `p`, `X_[p,q]` swaps entries `p` and `q`, and
`H_[p,q]` replaces them by `(v_p + v_q)/√2` and `(v_p - v_q)/√2`.  A signed
permutation of the entries keeps the least denominator exponent and moves
the numerators along; `H_[p,q]` on two odd numerators of the same class
(`u_p ≡ u_q (mod 2)`) makes both even at the same exponent.
-/
import QCert.HadamardPi.Column

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

section LevelVec

variable {R : Type*} [CommRing R] {m : ℕ}

theorem embedMat_transpose_mulVec (f : Fin m → Fin n) (v : Fin n → R) :
    (embedMat (R := R) f)ᵀ *ᵥ v = v ∘ f := by
  funext k
  simp only [mulVec, dotProduct, transpose_apply, embedMat, Function.comp]
  rw [Finset.sum_eq_single (f k)] <;> simp +contextual [eq_comm]

theorem levelMat_mulVec (f : Fin m → Fin n) (B : Matrix (Fin m) (Fin m) R) (v : Fin n → R) :
    levelMat f B *ᵥ v = v + embedMat f *ᵥ ((B - 1) *ᵥ (v ∘ f)) := by
  rw [levelMat, add_mulVec, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    embedMat_transpose_mulVec]

theorem embedMat_mulVec_two (p q : Fin n) (w : Fin 2 → R) (i : Fin n) :
    (embedMat ![p, q] *ᵥ w) i = (if p = i then w 0 else 0) + (if q = i then w 1 else 0) := by
  simp [mulVec, dotProduct, embedMat, Fin.sum_univ_two]

theorem embedMat_mulVec_one (p : Fin n) (w : Fin 1 → R) (i : Fin n) :
    (embedMat ![p] *ᵥ w) i = if p = i then w 0 else 0 := by
  simp [mulVec, dotProduct, embedMat]

end LevelVec

section Vec

variable (p q : Fin n) (v : Fin n → ℝ)

/-- `(-1)_[p]` on a column. -/
def zv : Fin n → ℝ := fun i => if i = p then -v p else v i

/-- `X_[p,q]` on a column. -/
def xv : Fin n → ℝ := fun i => if i = p then v q else if i = q then v p else v i

/-- `H_[p,q]` on a column. -/
noncomputable def hv : Fin n → ℝ :=
  fun i => if i = p then invSqrt2 * (v p + v q) else if i = q then invSqrt2 * (v p - v q) else v i

variable {p q}

theorem genMat_Z_mulVec : genMat invSqrt2 (Gen.Z p) *ᵥ v = zv p v := by
  funext i
  rw [genMat, levelMat_mulVec, Pi.add_apply, embedMat_mulVec_one]
  simp only [zv, mulVec, dotProduct, Fin.sum_univ_one, Function.comp, Zmat]
  by_cases h : i = p
  · subst h; simp; ring
  · simp [h, Ne.symm h]

theorem genMat_X_mulVec (h : p < q) : genMat invSqrt2 (Gen.X p q h) *ᵥ v = xv p q v := by
  have hne : p ≠ q := ne_of_lt h
  funext i
  rw [genMat, levelMat_mulVec, Pi.add_apply, embedMat_mulVec_two]
  simp only [xv, mulVec, dotProduct, Fin.sum_univ_two, Function.comp, Xmat]
  by_cases h1 : i = p
  · subst h1; simp [Ne.symm hne]
  · by_cases h2 : i = q
    · subst h2; simp [hne, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem genMat_H_mulVec (h : p < q) : genMat invSqrt2 (Gen.H p q h) *ᵥ v = hv p q v := by
  have hne : p ≠ q := ne_of_lt h
  funext i
  rw [genMat, levelMat_mulVec, Pi.add_apply, embedMat_mulVec_two]
  simp only [hv, mulVec, dotProduct, Fin.sum_univ_two, Function.comp, Hmat]
  by_cases h1 : i = p
  · subst h1; simp [Ne.symm hne]; ring
  · by_cases h2 : i = q
    · subst h2; simp [hne, h1]; ring
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-- A generator on a column. -/
noncomputable def gv : Gen n → (Fin n → ℝ) → (Fin n → ℝ)
  | .Z p => zv p
  | .X p q _ => xv p q
  | .H p q _ => hv p q

theorem genMat_mulVec (g : Gen n) : genMat invSqrt2 g *ᵥ v = gv g v := by
  cases g with
  | Z p => exact genMat_Z_mulVec v
  | X p q h => exact genMat_X_mulVec v h
  | H p q h => exact genMat_H_mulVec v h

/-- The columns of `⟦g⟧ M` are the columns of `M` acted on by `g`. -/
theorem col_sem_mul (g : Gen n) (M : O n) (j : Fin n) :
    col (sem n g * M) j = gv g (col M j) := by
  rw [← genMat_mulVec]
  funext i
  simp [col, mul_apply, mulVec, dotProduct]

theorem col_lift_mul (w : Word (Gen n)) (M : O n) (j : Fin n) :
    col (FreeMonoid.lift (sem n) w * M) j = wordMat invSqrt2 w *ᵥ col M j := by
  funext i
  simp [col, mat_lift, mul_apply, mulVec, dotProduct]

end Vec

section Perm

variable {v : Fin n → ℝ}

/-- Signed permutations of the entries keep the denominator exponents. -/
theorem denV_signed {σ : Fin n → Fin n} (hσ : Function.Surjective σ) {ε : Fin n → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) {k : ℕ} :
    DenV (fun i => ε i * v (σ i)) k ↔ DenV v k := by
  constructor
  · intro h i
    obtain ⟨i', rfl⟩ := hσ i
    have := h i'
    rcases hε i' with he | he <;> simp only [he, one_mul, neg_one_mul] at this
    · exact this
    · simpa using this.neg
  · intro h i
    rcases hε i with he | he <;> simp only [he, one_mul, neg_one_mul]
    · exact h _
    · exact (h _).neg

theorem inRing_signed {σ : Fin n → Fin n} {ε : Fin n → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hv : InRing v) : InRing (fun i => ε i * v (σ i)) := fun i => by
  rcases hε i with he | he <;> simp only [he, one_mul, neg_one_mul]
  · exact hv _
  · exact ZInvSqrt2.neg_mem (hv _)

theorem lde_signed {σ : Fin n → Fin n} (hσ : Function.Surjective σ) {ε : Fin n → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hv : InRing v) :
    lde (fun i => ε i * v (σ i)) = lde v :=
  le_antisymm (lde_le ((denV_signed hσ hε).2 (denV_lde hv)))
    (lde_le ((denV_signed hσ hε).1 (denV_lde (inRing_signed hε hv))))

theorem num_signed {σ : Fin n → Fin n} (hσ : Function.Surjective σ) {ε : Fin n → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hv : InRing v) (i : Fin n) :
    num (fun i => ε i * v (σ i)) i = if ε i = 1 then num v (σ i) else -num v (σ i) := by
  have hv' := inRing_signed (σ := σ) hε hv
  apply toReal_injective
  rw [toReal_num hv', lde_signed hσ hε hv]
  rcases hε i with he | he
  · rw [if_pos he, toReal_num hv, he, one_mul]
  · rw [if_neg (by rw [he]; norm_num), map_neg, toReal_num hv, he]; ring

theorem xv_eq_signed (p q : Fin n) :
    xv p q v = fun i => (1 : ℝ) * v (Equiv.swap p q i) := by
  funext i
  simp only [xv, one_mul, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem zv_eq_signed (p : Fin n) :
    zv p v = fun i => (if i = p then (-1 : ℝ) else 1) * v (id i) := by
  funext i
  simp only [zv, id]
  split_ifs <;> simp_all

theorem inRing_xv (p q : Fin n) (hv : InRing v) : InRing (xv p q v) := by
  rw [xv_eq_signed]; exact inRing_signed (fun _ => Or.inl rfl) hv

theorem inRing_zv (p : Fin n) (hv : InRing v) : InRing (zv p v) := by
  rw [zv_eq_signed]; exact inRing_signed (fun i => by split_ifs <;> simp) hv

theorem lde_xv (p q : Fin n) (hv : InRing v) : lde (xv p q v) = lde v := by
  rw [xv_eq_signed]; exact lde_signed (Equiv.swap p q).surjective (fun _ => Or.inl rfl) hv

theorem num_xv (p q : Fin n) (hv : InRing v) (i : Fin n) :
    num (xv p q v) i = num v (Equiv.swap p q i) := by
  rw [xv_eq_signed, num_signed (Equiv.swap p q).surjective (fun _ => Or.inl rfl) hv, if_pos rfl]

theorem lde_zv (p : Fin n) (hv : InRing v) : lde (zv p v) = lde v := by
  rw [zv_eq_signed]
  exact lde_signed Function.surjective_id (fun i => by split_ifs <;> simp) hv

theorem num_zv (p : Fin n) (hv : InRing v) (i : Fin n) :
    num (zv p v) i = if i = p then -num v i else num v i := by
  rw [zv_eq_signed, num_signed Function.surjective_id (fun i => by split_ifs <;> simp) hv]
  by_cases h : i = p <;> simp [h, show (-1 : ℝ) ≠ 1 by norm_num]

end Perm

section Pair

/-- Two numerators of the same residue mod 2 sum to twice an element. -/
theorem exists_half {u w : ℤ√2} (hre : Even (u.re + w.re)) (him : Even (u.im + w.im)) :
    ∃ z : ℤ√2, u + w = 2 * z := by
  obtain ⟨a, ha⟩ := hre; obtain ⟨b, hb⟩ := him
  exact ⟨⟨a, b⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> omega⟩

/-- `(x + y)/√2` at exponent `k`, for `x = u/√2^k` and `y = w/√2^k`. -/
theorem den_hsum {k : ℕ} {x y : ℝ} {u w : ℤ√2} (hx : toReal u = Real.sqrt 2 ^ k * x)
    (hy : toReal w = Real.sqrt 2 ^ k * y) :
    toReal (u + w) = Real.sqrt 2 ^ (k + 1) * (invSqrt2 * (x + y)) := by
  rw [map_add, hx, hy, pow_succ]
  have := sqrt2_mul_invSqrt2
  linear_combination (-(Real.sqrt 2 ^ k * (x + y))) * this

theorem den_hdiff {k : ℕ} {x y : ℝ} {u w : ℤ√2} (hx : toReal u = Real.sqrt 2 ^ k * x)
    (hy : toReal w = Real.sqrt 2 ^ k * y) :
    toReal (u - w) = Real.sqrt 2 ^ (k + 1) * (invSqrt2 * (x - y)) := by
  rw [map_sub, hx, hy, pow_succ]
  have := sqrt2_mul_invSqrt2
  linear_combination (-(Real.sqrt 2 ^ k * (x - y))) * this

/-- If `2 z = √2^{k+1} x`, then `√2 z = √2^k x`: the numerator at exponent
`k` is `√2 z`, which is even. -/
theorem den_of_two_mul {k : ℕ} {x : ℝ} {z : ℤ√2}
    (h : toReal (2 * z) = Real.sqrt 2 ^ (k + 1) * x) :
    toReal (rt2 * z) = Real.sqrt 2 ^ k * x := by
  rw [map_mul, map_ofNat, pow_succ] at h
  rw [map_mul, toReal_rt2]
  apply mul_left_cancel₀ sqrt2_ne_zero
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination h + toReal z * h2

theorem even_re_rt2_mul (z : ℤ√2) : Even (rt2 * z).re := by
  rw [rt2_mul]; exact ⟨z.im, by ring⟩

end Pair

end QCert.HadamardPi
