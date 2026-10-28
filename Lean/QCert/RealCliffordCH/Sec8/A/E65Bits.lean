/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The swaps and negations of Appendix A.4.1 as signed permutations

The words `𝒲₁`, `𝒲₂` of Equations (36), (37) are built from the encodings
`E_{k,ℓ}(swap)` (`encSwap`) and `ℰ_{k,ℓ}(X)` (`encNeg`).  As signed
permutations of the indices they are the permutations of the basis states
that exchange the wires `ℓ + 1, ℓ` (`swapB`) and flip the wire `ℓ`
(`flipB`), with no sign: `SOp n B f σ` says that `B` sends the index of the
state `s` to that of `f s`, with sign `σ s` (`sop_encSwap`, `sop_encNeg`).

The letters of these encodings act on pairs of states differing in one
bit, the pairs of distinct letters disjoint; on natural-number letters
whose indices are states (`NL.rel` relabels them by `G⁻¹`) the signed
permutation of such a word is read off pair by pair (`zzS_spec`,
`zxPairs_spec`).
-/
import QCert.RealCliffordCH.Sec8.A.Push
import QCert.RealCliffordCH.Sec8.ESem.Encode

namespace QCert.RealCliffordCH.Sec8

/-! ## Bits -/

theorem bit_eq_toNat (q s : ℕ) : bit q s = (s.testBit q).toNat := by
  unfold bit; rw [Nat.toNat_testBit]

theorem eq_of_bits {s t : ℕ} (h : ∀ q, bit q s = bit q t) : s = t :=
  Nat.eq_of_testBit_eq fun q => by
    have := h q
    rw [bit_eq_toNat, bit_eq_toNat] at this
    revert this; cases s.testBit q <;> cases t.testBit q <;> simp

theorem bit_of_ge {n s q : ℕ} (hs : s < 2 ^ n) (hq : n ≤ q) : bit q s = 0 := by
  rw [bit_eq_toNat, testBit_of_lt hs hq]; rfl

theorem lt_of_bits {n s : ℕ} (h : ∀ q, n ≤ q → bit q s = 0) : s < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun q hq => by
    have := h q hq
    rw [bit_eq_toNat] at this
    revert this; cases s.testBit q <;> simp

theorem bit_add_pow2 {p u c : ℕ} (hu : bit p u = 0) (hc : c < 2) (q : ℕ) :
    bit q (u + c * 2 ^ p) = if q = p then c else bit q u := by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · simp only [zero_mul, add_zero]
    split_ifs with h
    · subst h; exact hu
    · rfl
  · simp only [one_mul]
    obtain ⟨h1, h2⟩ := bit_add_pow hu
    split_ifs with h
    · subst h; exact h1
    · rw [← bit_clr_ne p q _ h, h2]

/-! ## Flipping a wire and exchanging two adjacent wires -/

/-- The state `s` with its bit on wire `p` flipped. -/
def flipB (p s : ℕ) : ℕ := clr p s + (1 - bit p s) * 2 ^ p

/-- The state `s` with its bits on the wires `p`, `p + 1` exchanged. -/
def swapB (p s : ℕ) : ℕ := clr p (clr (p + 1) s) + bit p s * 2 ^ (p + 1) + bit (p + 1) s * 2 ^ p

/-- The transposition of `p` and `p + 1`. -/
def tauB (p q : ℕ) : ℕ := if q = p then p + 1 else if q = p + 1 then p else q

theorem bit_flipB (p s q : ℕ) : bit q (flipB p s) = if q = p then 1 - bit p s else bit q s := by
  unfold flipB
  rw [bit_add_pow2 (bit_clr p s) (by omega)]
  split_ifs with h
  · rfl
  · exact bit_clr_ne p q s h

theorem bit_flipB_self (p s : ℕ) : bit p (flipB p s) = 1 - bit p s := by
  rw [bit_flipB, if_pos rfl]

theorem bit_flipB_ne {p q : ℕ} (s : ℕ) (h : q ≠ p) : bit q (flipB p s) = bit q s := by
  rw [bit_flipB, if_neg h]

theorem clr_flipB (p s : ℕ) : clr p (flipB p s) = clr p s := by
  unfold flipB
  rcases (by have := bit_lt p s; omega : 1 - bit p s = 0 ∨ 1 - bit p s = 1) with h | h
  · rw [h, zero_mul, add_zero, clr_clr]
  · rw [h, one_mul]; exact (bit_add_pow (bit_clr p s)).2

theorem bit_swapB (p s q : ℕ) : bit q (swapB p s) = bit (tauB p q) s := by
  unfold swapB tauB
  have h0 : bit (p + 1) (clr p (clr (p + 1) s)) = 0 := by
    rw [bit_clr_ne p (p + 1) _ (by omega)]; exact bit_clr _ _
  have h1 : bit p (clr p (clr (p + 1) s) + bit p s * 2 ^ (p + 1)) = 0 := by
    rw [bit_add_pow2 h0 (bit_lt _ _), if_neg (by omega)]; exact bit_clr _ _
  rw [bit_add_pow2 h1 (bit_lt _ _), bit_add_pow2 h0 (bit_lt _ _)]
  by_cases hq : q = p
  · subst hq; simp
  · by_cases hq' : q = p + 1
    · subst hq'; simp
    · simp only [hq, hq', if_false]
      rw [bit_clr_ne p q _ hq, bit_clr_ne (p + 1) q _ hq']

theorem tauB_tauB (p q : ℕ) : tauB p (tauB p q) = q := by
  unfold tauB; split_ifs <;> omega

theorem flipB_flipB (p s : ℕ) : flipB p (flipB p s) = s :=
  eq_of_bits fun q => by
    by_cases h : q = p
    · subst h; rw [bit_flipB_self, bit_flipB_self]; have := bit_lt q s; omega
    · rw [bit_flipB_ne _ h, bit_flipB_ne _ h]

theorem flipB_comm (p p' s : ℕ) : flipB p (flipB p' s) = flipB p' (flipB p s) := by
  by_cases h : p = p'
  · subst h; rfl
  · exact eq_of_bits fun q => by simp only [bit_flipB]; split_ifs <;> omega

theorem swapB_swapB (p s : ℕ) : swapB p (swapB p s) = s :=
  eq_of_bits fun q => by rw [bit_swapB, bit_swapB, tauB_tauB]

theorem swapB_of_eq {p s : ℕ} (h : bit p s = bit (p + 1) s) : swapB p s = s :=
  eq_of_bits fun q => by
    rw [bit_swapB]; unfold tauB
    split_ifs with h1 h2
    · subst h1; exact h.symm
    · subst h2; exact h
    · rfl

theorem swapB_of_ne {p s : ℕ} (h : bit p s ≠ bit (p + 1) s) :
    swapB p s = flipB (p + 1) (flipB p s) :=
  eq_of_bits fun q => by
    have h0 := bit_lt p s; have h1 := bit_lt (p + 1) s
    rw [bit_swapB]; unfold tauB; simp only [bit_flipB]
    split_ifs <;> omega

theorem flipB_lt {n p s : ℕ} (hs : s < 2 ^ n) (hp : p < n) : flipB p s < 2 ^ n :=
  lt_of_bits fun q hq => by rw [bit_flipB_ne _ (by omega)]; exact bit_of_ge hs hq

theorem swapB_lt {n p s : ℕ} (hs : s < 2 ^ n) (hp : p + 1 < n) : swapB p s < 2 ^ n :=
  lt_of_bits fun q hq => by
    rw [bit_swapB, show tauB p q = q by unfold tauB; split_ifs <;> omega]
    exact bit_of_ge hs hq

/-! ## Decompositions of a state around a wire -/

theorem div_succ_eq (p s : ℕ) : s / 2 ^ p = s / 2 ^ (p + 1) * 2 + bit p s := by
  unfold bit
  have := Nat.div_add_mod (s / 2 ^ p) 2
  rw [div_two_pow_add s p 1, pow_one] at *
  omega

theorem mod_succ_eq (p s : ℕ) : s % 2 ^ (p + 1) = bit p s * 2 ^ p + s % 2 ^ p := by
  rw [Nat.mod_pow_succ]; unfold bit; ring

/-- `clr p s` is `s` without its bit on wire `p`. -/
theorem clr_def (p s : ℕ) : clr p s = s / 2 ^ (p + 1) * 2 ^ (p + 1) + s % 2 ^ p := by
  unfold clr; ring

/-- The bits of `(K * x + r) * 2^p + y`, `y < 2^p`. -/
theorem bit_lin (p K x r : ℕ) {y : ℕ} (hy : y < 2 ^ p) :
    bit p ((K * x + r) * 2 ^ p + y) = (K * x + r) % 2 ∧
      bit (p + 1) ((K * x + r) * 2 ^ p + y) = (K * x + r) / 2 % 2 := by
  refine ⟨bit_mul_add₀ _ _ hy, ?_⟩
  rw [bit_mul_add p 1 _ hy, pow_one]

theorem lin_inj {p K x x' r : ℕ} (hK : 0 < K) {y y' : ℕ} (hy : y < 2 ^ p) (hy' : y' < 2 ^ p)
    (h : (K * x + r) * 2 ^ p + y = (K * x' + r) * 2 ^ p + y') : x = x' ∧ y = y' := by
  have h1 := div_mod_mul_add (K * x + r) hy
  have h2 := div_mod_mul_add (K * x' + r) hy'
  rw [h] at h1
  have e1 := h1.1.symm.trans h2.1
  have e2 := h1.2.symm.trans h2.2
  refine ⟨?_, e2⟩
  have : K * x = K * x' := by omega
  exact Nat.eq_of_mul_eq_mul_left hK this

theorem mem_grid_map {k ℓ u : ℕ} {f : ℕ × ℕ → ℕ} :
    u ∈ (grid k ℓ).map f ↔ ∃ x < 2 ^ k, ∃ y < 2 ^ ℓ, f (x, y) = u := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨x, y⟩, hq, rfl⟩
    rw [mem_grid] at hq
    exact ⟨x, hq.1, y, hq.2, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), mem_grid.2 ⟨hx, hy⟩, rfl⟩

theorem grid_map_nodup {k ℓ : ℕ} {f : ℕ × ℕ → ℕ}
    (h : ∀ x < 2 ^ k, ∀ y < 2 ^ ℓ, ∀ x' < 2 ^ k, ∀ y' < 2 ^ ℓ, f (x, y) = f (x', y') →
      x = x' ∧ y = y') : ((grid k ℓ).map f).Nodup := by
  refine List.Nodup.map_on ?_ (grid_nodup k ℓ)
  rintro ⟨x, y⟩ hq ⟨x', y'⟩ hq' e
  rw [mem_grid] at hq hq'
  obtain ⟨rfl, rfl⟩ := h x hq.1 y hq.2 x' hq'.1 y' hq'.2 e
  rfl

end QCert.RealCliffordCH.Sec8
