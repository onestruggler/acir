/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: Lemma 8.6 for `H` and `CH`

The letters of the encoding of `H` on wire `ℓ + 1` are
`H_[G⁻¹(x00y), G⁻¹(x10y)]H_[G⁻¹(x01y), G⁻¹(x11y)]`: by `dec_hh_one` the
multi-controlled `H` with its box on wire `ℓ`, controlled by `x` and `y`.
They merge by (310) into the multi-controlled `H` with no control, which is
`H` on wire `ℓ + 1` (`mch 0 = shift h`).  For `CH` there is one control
left (`mch 1 = shift ch`); on wire `0` the box is on the top wire
(`dec_hh_two`).
-/
import QCert.RealCliffordCH.Sec8.E.EncH

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

theorem mc_black2 {n : ℕ} (K : Kind) {bx hw : ℕ} {F : List ℕ} (hF : F.Pairwise (· < ·))
    (hFn : ∀ a ∈ F, a < n) (hbF : bx ∉ F) (hhF : hw ∉ F) :
    mc n K [bx, hw] (blackL F) = canonAt n K F.length (bx :: hw :: F) := by
  have hcw : ctrlWires n [bx, hw] (blackL F) = F := by
    apply eq_of_lt_mem (List.Pairwise.filter _ List.pairwise_lt_range) hF
    intro x
    show x ∈ ctrlWires n [bx, hw] (blackL F) ↔ x ∈ F
    rw [MS.mem_ctrlWires]
    simp only [blackL, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨_, h, _⟩; by_contra hx; simp [hx] at h
    · intro hx
      exact ⟨hFn x hx, by simp [hx], by rintro (e | e) <;> subst e <;> contradiction⟩
  have hww : whiteWires n [bx, hw] (blackL F) = [] := by
    unfold whiteWires
    rw [List.filter_eq_nil_iff]
    intro j _
    unfold blackL; split_ifs <;> simp
  unfold mc colourW
  rw [hcw, hww]
  simp [drawn]

/-- The multi-controlled `H` with no control is `H` on its `H` wire. -/
theorem hg0_h {n bx hw : ℕ} (hbh : bx ≠ hw) (hb : bx < n) (hh : hw < n) :
    Derivable (theory n) (mc n .hg [bx, hw] (blackL [])) (place1 n hw h) := by
  rw [mc_black2 .hg (by simp) (by simp) (by simp) (by simp)]
  exact (placeG_shift_cons (n := n) (h : Circ 1) (p := bx) (ps := [hw]) (by simp [hbh])
    (by simp [hb, hh]) rfl).trans (place1_placeG h n hw hh).symm

/-- The multi-controlled `H` with one black control above its `H` wire is `CH`. -/
theorem hg1_ch {n bx hw : ℕ} (hbh : bx ≠ hw) (hbh' : bx ≠ hw + 1) (hb : bx < n) (hh : hw + 1 < n) :
    Derivable (theory n) (mc n .hg [bx, hw] (blackL [hw + 1])) (place2 n hw ch) := by
  rw [mc_black2 .hg (by simp) (by simp; omega) (by simp; omega) (by simp)]
  exact (placeG_shift_cons (n := n) (ch : Circ 2) (p := bx) (ps := [hw, hw + 1]) (by simp; omega)
    (by intro q hq; simp at hq; omega) rfl).trans (place2_placeG ch n hw (by omega)).symm

theorem ctl2Of_eq_bitsOn {n : ℕ} (ws : List ℕ) (hnd : ws.Nodup) (base : ℕ → Option Bool)
    (bx hw s i : ℕ) (hbw : bx ∉ ws) (hhw : hw ∉ ws)
    (hws : ∀ r < ws.length, s.testBit (ws.getD r 0) = i.testBit r)
    (hbase : ∀ j < n, j ∉ ws → ctl2Of s bx hw j = base j) :
    ∀ j < n, ctl2Of s bx hw j = bitsOn ws i base j := by
  intro j hj
  by_cases hjw : j ∈ ws
  · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hjw
    rw [← List.getD_eq_getElem _ 0 hr, bitsOn_getD ws i base r hnd hr, ← hws r hr]
    have hne : ¬ (ws.getD r 0 = bx ∨ ws.getD r 0 = hw) := by
      rintro (e | e)
      · apply hbw; rw [← e, List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
      · apply hhw; rw [← e, List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
    simp only [ctl2Of, hne, if_false, bitOf_eq]
    cases s.testBit (ws.getD r 0) <;> rfl
  · rw [bitsOn_of_not_mem ws i base j hjw]
    exact hbase j hj hjw

/-- A word of letters decoding to multi-controlled `H` gates on the wires
`bx`, `hw` over every colouring of the wires `ws` merges into one. -/
theorem decode_hg_list {M : ℕ} (ih : IH (M + 3)) {bx hw : ℕ} (hb : bx < M + 3) (hh : hw < M + 3)
    (hbh : bx ≠ hw) (ws : List ℕ) (hnd : ws.Nodup) (hbw : bx ∉ ws) (hhw : hw ∉ ws)
    (hws : ∀ w ∈ ws, w < M + 3) (base : ℕ → Option Bool) (hb0 : base bx = none)
    (hh0 : base hw = none) (F : ℕ → PG (2 ^ (M + 3))) (sOf : ℕ → ℕ)
    (hF : ∀ i < 2 ^ ws.length, dec (M + 3) (F i) = mc (M + 3) .hg [bx, hw] (ctl2Of (sOf i) bx hw))
    (hs : ∀ i < 2 ^ ws.length, ∀ j < M + 3, ctl2Of (sOf i) bx hw j = bitsOn ws i base j) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf ((List.range (2 ^ ws.length)).map F)))
      (mc (M + 3) .hg [bx, hw] (idleOn ws base)) := by
  rw [decW_wordOf, List.map_map]
  refine Derivable.trans ?_ (mergeListGen .hg [bx, hw] (fun c hc w hwt hwN b =>
    mergeHgAt ih hb hh hbh c (hc bx (by simp)) (hc hw (by simp)) (fun e => hwt (by simp [e]))
      (fun e => hwt (by simp [e])) hwN b) ws base hnd
    (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> assumption) hws
    (by intro t ht; simp at ht; rcases ht with rfl | rfl <;> assumption))
  apply prod_map_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  show Derivable _ (dec (M + 3) (F i)) _
  rw [hF i hi', Net.mc_congr (M + 3) .hg [bx, hw] (hs i hi')]

/-- `H` on wire `ℓ + 1`. -/
theorem lemma86_H_hi {M : ℕ} (ih : IH (M + 3)) (ℓ : ℕ) (hj : ℓ + 1 < M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.H (ℓ + 1)))))
      ((L.H (ℓ + 1)).circ (M + 3)) := by
  set k := M + 3 - 1 - (ℓ + 1) with hk
  have hn : M + 3 = ℓ + 2 + k := by omega
  set ws := lowHigh ℓ 2 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 2 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 0 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 2 then (0 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 2)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hb0 : ∀ i, (sOf i).testBit ℓ = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega)]; simp
  have hb1 : ∀ i, (sOf i).testBit (ℓ + 1) = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega)]; simp
  have hb0' : ∀ i, (sOf i ^^^ 2 ^ (ℓ + 1)).testBit ℓ = false := fun i => by
    rw [testBit_xor_pow_ne (by omega), hb0]
  set F : ℕ → PG (2 ^ (M + 3)) := fun i => PG.hh (gx (M + 3) (sOf i))
    (gx (M + 3) (sOf i ^^^ 2 ^ (ℓ + 1))) (gx (M + 3) (sOf i ^^^ 2 ^ ℓ))
    (gx (M + 3) (sOf i ^^^ 2 ^ (ℓ + 1) ^^^ 2 ^ ℓ)) with hF
  have hl : encL (M + 3) (.H (ℓ + 1)) = (List.range (2 ^ ws.length)).map F := by
    simp only [encL, enc1, grid_eq, List.map_map]
    rw [hlen, ← hk, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, hF]
    congr 2
    · simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb1 i)]; simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb0 i)]; simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb0' i), ← add_two_pow_eq_xor (hb1 i)]; simp only [hsOf]; ring
  rw [hl]
  have hnone : ∀ w ∈ ws, blackL [] w = none := fun w _ => rfl
  have hd := decode_hg_list ih (bx := ℓ) (hw := ℓ + 1) (by omega) hj (by omega) ws
    (lowHigh_nodup ℓ 2 k) (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
    (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega) (blackL []) rfl rfl F sOf
    (by
      intro i hi
      have hs := state_lt i 0 ℓ 2 k (by rw [hlen] at hi; exact hi) (by norm_num)
      rw [← hn] at hs
      exact dec_hh_one (k := M + 1) (s := sOf i) (u := ℓ + 1) (w := ℓ) (by omega) hj hs (hb1 i) (hb0 i))
    (by
      intro i hi
      apply ctl2Of_eq_bitsOn ws (lowHigh_nodup ℓ 2 k) _ ℓ (ℓ + 1) (sOf i) i
        (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
      · intro r hr
        rw [hlen] at hr
        exact testBit_state i 0 ℓ 2 k r hr (by norm_num)
      · intro j hj' hjw
        rw [hws_def, mem_lowHigh] at hjw
        have : j = ℓ ∨ j = ℓ + 1 := by omega
        simp [ctl2Of, this, blackL])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd.trans (hg0_h (by omega) (by omega) hj)

/-- `CH` with its `H` on wire `ℓ + 1` and its control on wire `ℓ + 2`. -/
theorem lemma86_CH_hi {M : ℕ} (ih : IH (M + 3)) (ℓ : ℕ) (hj : ℓ + 3 ≤ M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.K (ℓ + 1)))))
      ((L.K (ℓ + 1)).circ (M + 3)) := by
  set k := M + 3 - 2 - (ℓ + 1) with hk
  have hn : M + 3 = ℓ + 3 + k := by omega
  set ws := lowHigh ℓ 3 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 3 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 3) + 4 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 3 then (4 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 3)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hb0 : ∀ i, (sOf i).testBit ℓ = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), Nat.sub_self]; decide
  have hb1 : ∀ i, (sOf i).testBit (ℓ + 1) = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), show ℓ + 1 - ℓ = 1 by omega]; decide
  have hb2 : ∀ i, (sOf i).testBit (ℓ + 2) = true := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), show ℓ + 2 - ℓ = 2 by omega]; decide
  have hb0' : ∀ i, (sOf i ^^^ 2 ^ (ℓ + 1)).testBit ℓ = false := fun i => by
    rw [testBit_xor_pow_ne (by omega), hb0]
  set F : ℕ → PG (2 ^ (M + 3)) := fun i => PG.hh (gx (M + 3) (sOf i))
    (gx (M + 3) (sOf i ^^^ 2 ^ (ℓ + 1))) (gx (M + 3) (sOf i ^^^ 2 ^ ℓ))
    (gx (M + 3) (sOf i ^^^ 2 ^ (ℓ + 1) ^^^ 2 ^ ℓ)) with hF
  have hl : encL (M + 3) (.K (ℓ + 1)) = (List.range (2 ^ ws.length)).map F := by
    simp only [encL, enc2, grid_eq, List.map_map]
    rw [hlen, ← hk, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, hF]
    congr 2
    · simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb1 i)]; simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb0 i)]; simp only [hsOf]; ring
    · rw [← add_two_pow_eq_xor (hb0' i), ← add_two_pow_eq_xor (hb1 i)]; simp only [hsOf]; ring
  rw [hl]
  have hnone : ∀ w ∈ ws, blackL [ℓ + 2] w = none := by
    intro w hw
    rw [hws_def, mem_lowHigh] at hw
    simp [blackL]; omega
  have hd := decode_hg_list ih (bx := ℓ) (hw := ℓ + 1) (by omega) (by omega) (by omega) ws
    (lowHigh_nodup ℓ 3 k) (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
    (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega) (blackL [ℓ + 2]) (by simp [blackL])
    (by simp [blackL]) F sOf
    (by
      intro i hi
      have hs := state_lt i 4 ℓ 3 k (by rw [hlen] at hi; exact hi) (by norm_num)
      rw [← hn] at hs
      exact dec_hh_one (k := M + 1) (s := sOf i) (u := ℓ + 1) (w := ℓ) (by omega) (by omega) hs
        (hb1 i) (hb0 i))
    (by
      intro i hi
      apply ctl2Of_eq_bitsOn ws (lowHigh_nodup ℓ 3 k) _ ℓ (ℓ + 1) (sOf i) i
        (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
      · intro r hr
        rw [hlen] at hr
        exact testBit_state i 4 ℓ 3 k r hr (by norm_num)
      · intro j hj' hjw
        rw [hws_def, mem_lowHigh] at hjw
        have : j = ℓ ∨ j = ℓ + 1 ∨ j = ℓ + 2 := by omega
        rcases this with rfl | rfl | rfl
        · simp [ctl2Of, blackL]
        · simp [ctl2Of, blackL]
        · simp [ctl2Of, blackL, bitOf_eq, hb2])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd.trans (hg1_ch (by omega) (by omega) (by omega) (by omega))

/-- `H` on wire `0`: the box is on the top wire. -/
theorem lemma86_H_lo {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.H 0))))
      ((L.H 0).circ (M + 3)) := by
  set k := M + 2 with hk
  set ws := lowHigh 0 1 (k - 1) with hws_def
  have hlen : ws.length = k - 1 := by rw [hws_def, lowHigh_length]; omega
  set sOf : ℕ → ℕ := fun i => i / 2 ^ 0 * 2 ^ (0 + 1) + 0 * 2 ^ 0 + i % 2 ^ 0 with hsOf
  have hsv : ∀ i, sOf i = i * 2 := fun i => by simp [hsOf, Nat.mod_one]
  have hslt : ∀ i, i < 2 ^ (k - 1) → sOf i < 2 ^ k := fun i hi => by
    have := state_lt i 0 0 1 (k - 1) (by simpa using hi) (by norm_num)
    rw [show 0 + 1 + (k - 1) = k by omega] at this
    exact this
  have hb0 : ∀ i, (sOf i).testBit 0 = false := fun i => by
    rw [hsv, Nat.testBit_zero]; simp
  set F : ℕ → PG (2 ^ (M + 3)) := fun i => PG.hh (gx (M + 3) (sOf i))
    (gx (M + 3) (sOf i ^^^ 2 ^ 0)) (gx (M + 3) (sOf i ^^^ 2 ^ k))
    (gx (M + 3) (sOf i ^^^ 2 ^ k ^^^ 2 ^ 0)) with hF
  have hl : encL (M + 3) (.H 0) = (List.range (2 ^ ws.length)).map F := by
    simp only [encL, enc1]
    rw [show M + 3 - 1 - 0 = k by omega, hlen]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    have hbk : (sOf i).testBit k = false := testBit_of_lt (hslt i hi') le_rfl
    have hb0' : (sOf i ^^^ 2 ^ k).testBit 0 = false := by
      rw [testBit_xor_pow_ne (by omega), hb0]
    simp only [hF]
    congr 2
    · rw [hsv]; ring
    · rw [← add_two_pow_eq_xor (hb0 i), hsv]; ring
    · rw [← add_two_pow_eq_xor hbk, hsv]; ring
    · rw [← add_two_pow_eq_xor hb0', ← add_two_pow_eq_xor hbk, hsv]; ring
  rw [hl]
  have hnone : ∀ w ∈ ws, blackL [] w = none := fun w _ => rfl
  have hd := decode_hg_list ih (bx := k) (hw := 0) (by omega) (by omega) (by omega) ws
    (lowHigh_nodup 0 1 (k - 1)) (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
    (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega) (blackL []) rfl rfl F sOf
    (by
      intro i hi
      rw [hlen] at hi
      have hs : sOf i < 2 ^ (M + 1 + 2) :=
        lt_of_lt_of_le (hslt i hi) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact dec_hh_two (k := M + 1) (s := sOf i) (u := k) (w := 0) (by omega) (by omega) hs
        (testBit_of_lt (hslt i hi) le_rfl) (hb0 i))
    (by
      intro i hi
      apply ctl2Of_eq_bitsOn ws (lowHigh_nodup 0 1 (k - 1)) _ k 0 (sOf i) i
        (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
      · intro r hr
        rw [hlen] at hr
        exact testBit_state i 0 0 1 (k - 1) r (by omega) (by norm_num)
      · intro j hj' hjw
        rw [hws_def, mem_lowHigh] at hjw
        have : j = k ∨ j = 0 := by omega
        simp [ctl2Of, this, blackL])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd.trans (hg0_h (by omega) (by omega) (by omega))

/-- `CH` with its `H` on wire `0` and its control on wire `1`: the box is on
the top wire. -/
theorem lemma86_CH_lo {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.K 0))))
      ((L.K 0).circ (M + 3)) := by
  set k := M + 1 with hk
  set ws := lowHigh 0 2 (k - 1) with hws_def
  have hlen : ws.length = k - 1 := by rw [hws_def, lowHigh_length]; omega
  set sOf : ℕ → ℕ := fun i => i / 2 ^ 0 * 2 ^ (0 + 2) + 2 * 2 ^ 0 + i % 2 ^ 0 with hsOf
  have hsv : ∀ i, sOf i = i * 4 + 2 := fun i => by simp [hsOf, Nat.mod_one]
  have hslt : ∀ i, i < 2 ^ (k - 1) → sOf i < 2 ^ (k + 1) := fun i hi => by
    have := state_lt i 2 0 2 (k - 1) (by simpa using hi) (by norm_num)
    rw [show 0 + 2 + (k - 1) = k + 1 by omega] at this
    exact this
  have hb0 : ∀ i, (sOf i).testBit 0 = false := fun i => by
    rw [hsv, Nat.testBit_zero]; simp only [decide_eq_false_iff_not]; omega
  have hb1 : ∀ i, (sOf i).testBit 1 = true := fun i => by
    rw [hsv, Nat.testBit_add_one, Nat.testBit_zero]; simp only [decide_eq_true_eq]; omega
  set F : ℕ → PG (2 ^ (M + 3)) := fun i => PG.hh (gx (M + 3) (sOf i))
    (gx (M + 3) (sOf i ^^^ 2 ^ 0)) (gx (M + 3) (sOf i ^^^ 2 ^ (k + 1)))
    (gx (M + 3) (sOf i ^^^ 2 ^ (k + 1) ^^^ 2 ^ 0)) with hF
  have hl : encL (M + 3) (.K 0) = (List.range (2 ^ ws.length)).map F := by
    simp only [encL, enc2]
    rw [show M + 3 - 2 - 0 = k by omega, hlen]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.1 hi
    have hbk : (sOf i).testBit (k + 1) = false := testBit_of_lt (hslt i hi') le_rfl
    have hb0' : (sOf i ^^^ 2 ^ (k + 1)).testBit 0 = false := by
      rw [testBit_xor_pow_ne (by omega), hb0]
    simp only [hF]
    congr 2
    · rw [hsv]; ring
    · rw [← add_two_pow_eq_xor (hb0 i), hsv]; ring
    · rw [← add_two_pow_eq_xor hbk, hsv]; ring
    · rw [← add_two_pow_eq_xor hb0', ← add_two_pow_eq_xor hbk, hsv]; ring
  rw [hl]
  have hnone : ∀ w ∈ ws, blackL [1] w = none := by
    intro w hw
    rw [hws_def, mem_lowHigh] at hw
    simp [blackL]; omega
  have hd := decode_hg_list ih (bx := k + 1) (hw := 0) (by omega) (by omega) (by omega) ws
    (lowHigh_nodup 0 2 (k - 1)) (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
    (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega) (blackL [1]) (by simp [blackL])
    (by simp [blackL]) F sOf
    (by
      intro i hi
      rw [hlen] at hi
      have hs : sOf i < 2 ^ (M + 1 + 2) :=
        lt_of_lt_of_le (hslt i hi) (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact dec_hh_two (k := M + 1) (s := sOf i) (u := k + 1) (w := 0) (by omega) (by omega) hs
        (testBit_of_lt (hslt i hi) le_rfl) (hb0 i))
    (by
      intro i hi
      apply ctl2Of_eq_bitsOn ws (lowHigh_nodup 0 2 (k - 1)) _ (k + 1) 0 (sOf i) i
        (by rw [hws_def, mem_lowHigh]; omega) (by rw [hws_def, mem_lowHigh]; omega)
      · intro r hr
        rw [hlen] at hr
        exact testBit_state i 2 0 2 (k - 1) r (by omega) (by norm_num)
      · intro j hj' hjw
        rw [hws_def, mem_lowHigh] at hjw
        have : j = k + 1 ∨ j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl | rfl
        · simp [ctl2Of, blackL]
        · simp [ctl2Of, blackL]
        · simp [ctl2Of, blackL, bitOf_eq, hb1, show (1 : ℕ) ≠ k + 1 by omega])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd.trans (hg1_ch (by omega) (by omega) (by omega) (by omega))

end QCert.RealCliffordCH.Sec8.E
