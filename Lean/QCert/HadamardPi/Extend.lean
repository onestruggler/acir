/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Extending a window: entries forced by the parity of the classes

Clément's Lemma 2.1, at any exponent: the numerators `U` of a unit vector at
an exponent `K ≥ 1` (`√2^K v = U`, not necessarily the least one) have
evenly many odd ones, and evenly many of each class (`even_class_counts`).

Applied to a state `u = run D s` reached by a word `D` acting on a window
`W`, at the exponent `K = k − δ` (`k` that of `s`): outside the window the
column of `u` is that of `s`, so its numerators there are those of `s`
divided by `√2^δ`.  If the window has an odd number of odd numerators of
some class, so does the rest of the column, which therefore holds an entry
of `s` of depth exactly `δ` (`√2^δ` times an odd numerator) of that class
(`exists_tail_entry`).  The tree nodes of Case 3.4 supply `D`, `W`, `δ`, the
class and the window's numerators; Clément uses this with `δ = 1`
(Subcase 3.4.2: two entries `√2 × odd`), and `δ = 2` and `δ = 3`
(Lemma 5.13).
-/
import QCert.HadamardPi.Good

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-- Numerators of a unit vector at any positive exponent. -/
theorem sum_sq_at {v : Fin n → ℝ} (hu : IsUnitVec v) {K : ℕ} {U : Fin n → ℤ√2}
    (hU : ∀ i, toReal (U i) = Real.sqrt 2 ^ K * v i) : ∑ i, U i * U i = 2 ^ K := by
  apply toReal_injective
  rw [map_sum, map_pow, map_ofNat]
  simp only [map_mul, hU]
  have : ∑ i, Real.sqrt 2 ^ K * v i * (Real.sqrt 2 ^ K * v i) =
      (Real.sqrt 2 ^ K) ^ 2 * ∑ i, v i * v i := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, hu, mul_one, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]

/-- Clément's Lemma 2.1 at any exponent `K ≥ 1`: evenly many odd numerators
in each class. -/
theorem even_class_counts {v : Fin n → ℝ} (hu : IsUnitVec v) {K : ℕ} (hK : 1 ≤ K)
    {U : Fin n → ℤ√2} (hU : ∀ i, toReal (U i) = Real.sqrt 2 ^ K * v i) (γ : Bool) :
    Even (univ.filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)).card := by
  classical
  have hs := sum_sq_at hu hU
  have h1 := even_card_odd_odd U hs
  cases γ with
  | true => simpa using h1
  | false =>
    have h0 := even_card_odd_re U hK hs
    have hsub : (univ.filter fun i => Odd (U i).re ∧ Odd (U i).im) ⊆
        univ.filter fun i => Odd (U i).re := fun i hi => by
      rw [mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
    have heq : (univ.filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ false = true)) =
        (univ.filter fun i => Odd (U i).re) \ (univ.filter fun i => Odd (U i).re ∧ Odd (U i).im) := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_sdiff]; tauto
    rw [heq, card_sdiff_of_subset hsub, Nat.even_sub (card_le_card hsub)]
    exact iff_of_true h0 h1

theorem gv_out {g : Gen n} {i : Fin n} (h : i ∉ g.idx) (y : Fin n → ℝ) : gv g y i = y i := by
  cases g with
  | Z p => simp only [Gen.idx, mem_singleton] at h; simp [gv, zv, h]
  | X p q _ => simp only [Gen.idx, mem_insert, mem_singleton, not_or] at h; simp [gv, xv, h.1, h.2]
  | H p q _ => simp only [Gen.idx, mem_insert, mem_singleton, not_or] at h; simp [gv, hv, h.1, h.2]

theorem wv_out {i : Fin n} : ∀ (w : List (Gen n)), (∀ g ∈ w, i ∉ g.idx) →
    ∀ x : Fin n → ℝ, wv (ofList w) x i = x i
  | [], _, x => by simp
  | g :: w, h, x => by
    rw [ofList_cons, wv_mul, wv_of, gv_out (h g List.mem_cons_self)]
    exact wv_out w (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) x

open Classical in
/-- An entry outside a window, forced by the parity of a class. -/
theorem exists_tail_entry {s : O n} (hs : s ≠ 1) {D : List (Gen n)} (W : Finset (Fin n))
    (hW : ∀ g ∈ D, ∀ i ∈ g.idx, i ∈ W) {K δ : ℕ} (hK : 1 ≤ K)
    (hKδ : K + δ = lde (col s (pj s (piv_pos hs))))
    (U : Fin n → ℤ√2)
    (hU : ∀ i, toReal (U i) = Real.sqrt 2 ^ K * col (run D s) (pj s (piv_pos hs)) i)
    (γ : Bool) (hodd : Odd (W.filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)).card) :
    ∃ i, i ∉ W ∧ Odd (U i).re ∧ (Odd (U i).im ↔ γ = true) ∧
      rt2 ^ δ * U i = num (col s (pj s (piv_pos hs))) i := by
  set j := pj s (piv_pos hs)
  have hu : IsUnitVec (col (run D s) j) := col_unit _ _
  have hev := even_class_counts hu hK hU γ
  -- the class count splits between the window and the rest
  have hsplit := card_filter_split W fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)
  have hrest : ((univ \ W).filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)).Nonempty := by
    rw [← card_pos]
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0, add_zero] at hsplit
    rw [hsplit] at hev
    exact (Nat.not_even_iff_odd.2 hodd) hev
  obtain ⟨i, hi⟩ := hrest
  rw [mem_filter, mem_sdiff] at hi
  obtain ⟨⟨-, hiW⟩, hodd', hcls⟩ := hi
  refine ⟨i, hiW, hodd', hcls, ?_⟩
  -- outside the window the column of `run D s` is that of `s`
  have hcol : col (run D s) j i = col s j i := by
    rw [run_eq_lift, col_lift_mul']
    exact wv_out D (fun g hg hig => hiW (hW g hg i hig)) _
  have hR : InRing (col s j) := col_inRing s j
  apply toReal_injective
  rw [map_mul, map_pow, toReal_rt2, hU i, hcol, toReal_num hR, ← hKδ, pow_add]
  ring

end QCert.HadamardPi
