/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: Lemma 8.6 for `Z` and `CZ`

The encoding of `Z` on wire `j ≥ 1` is the product, over the bitstrings `x`
above and `y` below, of `(-1)_[G⁻¹(x10y)](-1)_[G⁻¹(x11y)]` (Definition 8.2):
by Lemma 8.4 the box on wire `j - 1` controlled by `x`, `1` on wire `j`, and
`y`.  In the order of the word, the index `i = x 2^(j-1) + y` runs through
`0, …, 2^(n-2) - 1`, its bits on the wires other than `j - 1`, `j` (`ws`), so
the boxes merge (`mergeListP`) into the box controlled by wire `j` alone,
which is `Z` on wire `j` (`box1_z`).  The other cases (`Z` on wire `0`,
`CZ`) are the same with other wires.
-/
import QCert.RealCliffordCH.Sec8.E.Lemma87
import QCert.RealCliffordCH.Sec8.E.Gates

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

/-! ## Colourings by the bits of an index -/

theorem bitsOn_getD : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) (r : ℕ), ws.Nodup →
    r < ws.length → bitsOn ws i base (ws.getD r 0) = some (i.testBit r)
  | [], _, _, _, _, h => absurd h (by simp)
  | w :: ws, i, base, 0, _, _ => by simp [bitsOn, setCtl, Nat.testBit_zero]
  | w :: ws, i, base, r + 1, hnd, h => by
    have hnd' := List.nodup_cons.1 hnd
    have hr : r < ws.length := by simpa using h
    have hne : ws.getD r 0 ≠ w := by
      intro e; apply hnd'.1; rw [← e, List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
    simp only [bitsOn, List.getD_cons_succ, setCtl, hne, if_false]
    rw [bitsOn_getD ws (i / 2) base r hnd'.2 hr, Nat.testBit_add_one]

theorem idleOn_of_none : ∀ (ws : List ℕ) (base : ℕ → Option Bool), (∀ w ∈ ws, base w = none) →
    idleOn ws base = base
  | [], _, _ => rfl
  | w :: ws, base, h => by
    have e : setCtl base w none = base := by
      funext j; simp only [setCtl]; split_ifs with hj
      · subst hj; exact (h j (by simp)).symm
      · rfl
    simp only [idleOn, e]
    exact idleOn_of_none ws base (fun x hx => h x (by simp [hx]))

theorem ctlOf_eq_bitsOn {n : ℕ} (ws : List ℕ) (hnd : ws.Nodup) (base : ℕ → Option Bool)
    (t0 s i : ℕ) (htw : t0 ∉ ws)
    (hws : ∀ r < ws.length, s.testBit (ws.getD r 0) = i.testBit r)
    (hbase : ∀ j < n, j ∉ ws → ctlOf s t0 j = base j) :
    ∀ j < n, ctlOf s t0 j = bitsOn ws i base j := by
  intro j hj
  by_cases hjw : j ∈ ws
  · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hjw
    rw [← List.getD_eq_getElem _ 0 hr, bitsOn_getD ws i base r hnd hr, ← hws r hr]
    have hne : ws.getD r 0 ≠ t0 := by
      intro e; apply htw; rw [← e, List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
    simp only [ctlOf, hne, if_false, bitOf_eq]
    cases s.testBit (ws.getD r 0) <;> rfl
  · rw [bitsOn_of_not_mem ws i base j hjw]
    exact hbase j hj hjw

/-! ## A word of letters `(-1)_[G⁻¹(s)](-1)_[G⁻¹(s xor 2^t)]` -/

/-- The decoding of the word of the letters `(-1)_[G⁻¹(s_i)](-1)_[G⁻¹(s_i xor 2^t)]`,
`i < 2^|ws|`, the bits of `s_i` off the wire `t` being the bits of `i` on the
wires `ws` and `base` elsewhere, is the box on wire `t` with the wires `ws` idle. -/
theorem decode_zz_list {M : ℕ} (ih : IH (M + 3)) {t : ℕ} (ht : t < M + 3) (ws : List ℕ)
    (hnd : ws.Nodup) (htw : t ∉ ws) (hws : ∀ w ∈ ws, w < M + 3) (base : ℕ → Option Bool)
    (hb : base t = none) (sOf : ℕ → ℕ)
    (hs : ∀ i < 2 ^ ws.length, sOf i < 2 ^ (M + 3) ∧ (sOf i).testBit t = false ∧
      ∀ j < M + 3, ctlOf (sOf i) t j = bitsOn ws i base j) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf ((List.range (2 ^ ws.length)).map fun i =>
        PG.zz (gx (M + 3) (sOf i)) (gx (M + 3) (sOf i ^^^ 2 ^ t)))))
      (mc (M + 3) .box [t] (idleOn ws base)) := by
  rw [decW_wordOf, List.map_map]
  refine Derivable.trans ?_ (mergeListP ih ht ws base hnd htw hws hb)
  apply prod_map_congr
  intro i hi
  obtain ⟨hsn, hst, hc⟩ := hs i (List.mem_range.1 hi)
  have h2t : 2 ^ t < 2 ^ (M + 3) := Nat.pow_lt_pow_right (by norm_num) ht
  have hs' : sOf i ^^^ 2 ^ t < 2 ^ (M + 3) := Nat.xor_lt_two_pow hsn h2t
  show Derivable _ (dec (M + 3) (PG.zz _ _)) _
  simp only [dec, gx_val hsn, gx_val hs']
  refine (lemma84 (k := M + 2) ih (by omega) hsn ht hst).trans ?_
  rw [show boxAt (M + 2 + 1) t (sOf i) = mc (M + 3) .box [t] (ctlOf (sOf i) t) from rfl,
    Net.mc_congr (M + 3) .box [t] hc]

/-! ## The grid of Definition 8.2 -/

theorem flatMap_range_map {β : Type*} (a b : ℕ) (hb : 0 < b) (g : ℕ → ℕ → β) :
    (List.range a).flatMap (fun x => (List.range b).map (fun y => g x y)) =
      (List.range (a * b)).map (fun i => g (i / b) (i % b)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append,
      List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    apply List.map_congr_left
    intro y hy
    have hy' := List.mem_range.1 hy
    simp only [Function.comp]
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hy']; simp
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy']

theorem grid_eq (k j : ℕ) :
    grid k j = (List.range (2 ^ k * 2 ^ j)).map fun i => (i / 2 ^ j, i % 2 ^ j) := by
  unfold grid
  exact flatMap_range_map (2 ^ k) (2 ^ j) (Nat.two_pow_pos j) (fun x y => (x, y))

/-! ## Bits of the states of Definition 8.2 -/

theorem testBit_mid (x a y ℓ m q : ℕ) (hy : y < 2 ^ ℓ) (ha : a < 2 ^ m) :
    (x * 2 ^ (ℓ + m) + a * 2 ^ ℓ + y).testBit q =
      if q < ℓ then y.testBit q else if q < ℓ + m then a.testBit (q - ℓ) else x.testBit (q - (ℓ + m)) := by
  have e : x * 2 ^ (ℓ + m) + a * 2 ^ ℓ + y = 2 ^ ℓ * (2 ^ m * x + a) + y := by ring
  rw [e, Nat.testBit_two_pow_mul_add _ hy]
  by_cases h1 : q < ℓ
  · simp [h1]
  · rw [if_neg h1, if_neg h1, Nat.testBit_two_pow_mul_add _ ha]
    by_cases h2 : q - ℓ < m
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega), show q - ℓ - m = q - (ℓ + m) by omega]

theorem lt_of_testBit_false {s n : ℕ} (h : ∀ q, n ≤ q → s.testBit q = false) : s < 2 ^ n :=
  Nat.lt_pow_two_of_testBit s fun q hq => h q hq

/-- The low wires `0, …, ℓ - 1` and the high wires from `ℓ + m` on, `k` of them. -/
def lowHigh (ℓ m k : ℕ) : List ℕ := List.range ℓ ++ (List.range k).map (· + (ℓ + m))

theorem lowHigh_length (ℓ m k : ℕ) : (lowHigh ℓ m k).length = ℓ + k := by simp [lowHigh]

theorem lowHigh_nodup (ℓ m k : ℕ) : (lowHigh ℓ m k).Nodup := by
  unfold lowHigh
  rw [List.nodup_append]
  refine ⟨List.nodup_range, (List.nodup_range).map (fun a b h => by simpa using h), ?_⟩
  intro a ha b hb e
  simp only [List.mem_range, List.mem_map] at ha hb
  obtain ⟨c, _, rfl⟩ := hb
  omega

theorem mem_lowHigh {ℓ m k j : ℕ} : j ∈ lowHigh ℓ m k ↔ j < ℓ ∨ (ℓ + m ≤ j ∧ j < ℓ + m + k) := by
  simp only [lowHigh, List.mem_append, List.mem_range, List.mem_map]
  constructor
  · rintro (h | ⟨c, hc, rfl⟩)
    · exact Or.inl h
    · right; omega
  · rintro (h | h)
    · exact Or.inl h
    · right; exact ⟨j - (ℓ + m), by omega, by omega⟩

theorem lowHigh_getD {ℓ m k r : ℕ} (hr : r < ℓ + k) :
    (lowHigh ℓ m k).getD r 0 = if r < ℓ then r else r + m := by
  unfold lowHigh
  rw [List.getD_eq_getElem?_getD]
  by_cases h : r < ℓ
  · rw [List.getElem?_append_left (by simpa using h)]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp [h]
    rw [List.getElem?_range (by omega)]; simp; omega

/-- The index `i = x 2^ℓ + y` and the state `x (a) y`, `a` on the `m` middle
wires: the bits of the state on the low and high wires are those of `i`. -/
theorem testBit_state (i a ℓ m k r : ℕ) (hr : r < ℓ + k) (ha : a < 2 ^ m) :
    (i / 2 ^ ℓ * 2 ^ (ℓ + m) + a * 2 ^ ℓ + i % 2 ^ ℓ).testBit ((lowHigh ℓ m k).getD r 0) =
      i.testBit r := by
  rw [lowHigh_getD hr, testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) ha]
  by_cases h : r < ℓ
  · simp [h, Nat.testBit_mod_two_pow]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega), Nat.testBit_div_two_pow,
      show r + m - (ℓ + m) + ℓ = r by omega]

theorem state_lt (i a ℓ m k : ℕ) (hi : i < 2 ^ (ℓ + k)) (ha : a < 2 ^ m) :
    i / 2 ^ ℓ * 2 ^ (ℓ + m) + a * 2 ^ ℓ + i % 2 ^ ℓ < 2 ^ (ℓ + m + k) := by
  apply lt_of_testBit_false
  intro q hq
  rw [testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) ha, if_neg (by omega),
    if_neg (by omega), Nat.testBit_div_two_pow]
  exact testBit_of_lt hi (by omega)


end QCert.RealCliffordCH.Sec8.E
