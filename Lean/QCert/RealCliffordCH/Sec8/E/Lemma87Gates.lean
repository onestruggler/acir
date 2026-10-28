/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: Lemma 8.6 for `Z` and `CZ`

The encoding of `Z` on wire `ℓ + 1` is the product, over the bitstrings `x`
above and `y` below, of `(-1)_[G⁻¹(x10y)](-1)_[G⁻¹(x11y)]` (Definition 8.2);
by Lemma 8.4 each is the box on wire `ℓ` controlled by `x`, `1` on wire
`ℓ + 1`, and `y`.  In the order of the word the index `i = x 2^ℓ + y` runs
through `0, …, 2^(n-2) - 1`, its bits on the other wires (`lowHigh`), so the
boxes merge into the box controlled by wire `ℓ + 1` alone, which is `Z` on
wire `ℓ + 1` (`box1_z`).  `Z` on wire `0` and `CZ` are the same with other
wires; on wire `0` the box is on the top wire.
-/
import QCert.RealCliffordCH.Sec8.E.EncZ

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

theorem add_two_pow_eq_xor {s t : ℕ} (h : s.testBit t = false) : s + 2 ^ t = s ^^^ 2 ^ t := by
  have hev : (s / 2 ^ t) % 2 = 0 := by
    have h0 : (s / 2 ^ t).testBit 0 = false := by rw [Nat.testBit_div_two_pow, Nat.zero_add]; exact h
    rw [Nat.testBit_zero] at h0
    simp at h0; omega
  have hm := Nat.mod_lt s (Nat.two_pow_pos t)
  apply Nat.eq_of_testBit_eq; intro q
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  have hd : s = 2 ^ t * (s / 2 ^ t) + s % 2 ^ t := (Nat.div_add_mod s (2 ^ t)).symm
  have e1 : s + 2 ^ t = 2 ^ t * (s / 2 ^ t + 1) + s % 2 ^ t := by
    conv_lhs => rw [hd]
    ring
  rw [e1, Nat.testBit_two_pow_mul_add _ hm]
  conv_rhs => rw [hd, Nat.testBit_two_pow_mul_add _ hm]
  by_cases hq : q < t
  · simp [hq, show t ≠ q by omega]
  · rw [if_neg hq, if_neg hq]
    by_cases hqt : q = t
    · subst hqt; simp [Nat.testBit_zero, Nat.add_mod, hev]
    · obtain ⟨u, hu⟩ : ∃ u, q - t = u + 1 := ⟨q - t - 1, by omega⟩
      rw [hu, Nat.testBit_add_one, Nat.testBit_add_one, show (s / 2 ^ t + 1) / 2 = s / 2 ^ t / 2 by omega]
      simp [show t ≠ q from Ne.symm hqt]

/-- `Z` on wire `ℓ + 1`. -/
theorem lemma86_Z_hi {M : ℕ} (ih : IH (M + 3)) (ℓ : ℕ) (hj : ℓ + 1 < M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.Z (ℓ + 1)))))
      ((L.Z (ℓ + 1)).circ (M + 3)) := by
  set k := M + 3 - 1 - (ℓ + 1) with hk
  have hn : M + 3 = ℓ + 2 + k := by omega
  set ws := lowHigh ℓ 2 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 2 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 2 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 2 then (2 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 2)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hbt : ∀ i, (sOf i).testBit ℓ = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), Nat.sub_self]; decide
  have hbt1 : ∀ i, (sOf i).testBit (ℓ + 1) = true := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), show ℓ + 1 - ℓ = 1 by omega]; decide
  have hl : encL (M + 3) (.Z (ℓ + 1)) = (List.range (2 ^ ws.length)).map fun i =>
      PG.zz (gx (M + 3) (sOf i)) (gx (M + 3) (sOf i ^^^ 2 ^ ℓ)) := by
    simp only [encL, enc1, grid_eq, List.map_map]
    rw [hlen, ← hk, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    congr 2
    · simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hbt i)]; simp only [hsOf]; ring
  rw [hl]
  have hb : blackL [ℓ + 1] ℓ = none := by simp [blackL]
  have hnone : ∀ w ∈ ws, blackL [ℓ + 1] w = none := by
    intro w hw
    rw [hws_def, mem_lowHigh] at hw
    simp [blackL]; omega
  have hd := decode_zz_list ih (t := ℓ) (by omega) ws (lowHigh_nodup ℓ 2 k)
    (by rw [hws_def, mem_lowHigh]; omega) (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega)
    (blackL [ℓ + 1]) hb sOf (by
      intro i hi
      refine ⟨?_, hbt i, ?_⟩
      · have := state_lt i 2 ℓ 2 k (by rw [hlen] at hi; exact hi) (by norm_num)
        rw [hn]; exact this
      · apply ctlOf_eq_bitsOn ws (lowHigh_nodup ℓ 2 k) _ ℓ (sOf i) i
          (by rw [hws_def, mem_lowHigh]; omega)
        · intro r hr
          rw [hlen] at hr
          exact testBit_state i 2 ℓ 2 k r hr (by norm_num)
        · intro j hj hjw
          rw [hws_def, mem_lowHigh] at hjw
          have : j = ℓ ∨ j = ℓ + 1 := by omega
          rcases this with rfl | rfl
          · simp [ctlOf, blackL]
          · simp [ctlOf, blackL, bitOf_eq, hbt1])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd.trans (box1_z (by omega) (by omega) hj)

end QCert.RealCliffordCH.Sec8.E
