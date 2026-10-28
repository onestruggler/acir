/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: gates placed on given wires with every other wire a control

When a multi-controlled gate has a control on every wire other than its
special wires `tg`, `placeG` places it on `tg` followed by the other wires in
increasing order (`rest n tg`), and the swap network of `placeG` only moves
the wires of `tg`: after them, the others are already in order
(`netPos_rest`).  So the decoded multi-controlled `H` of Definition 8.3,
placed by `placeAt2`, is `mc n .hg [b, h] c` (`dHH4_mc`), as the boxes and
`ZX` gates are (`Letters.dZZ1_mc`, `Letters.dZX1_mc`).
-/
import QCert.RealCliffordCH.Sec8.E.Letters

namespace QCert.RealCliffordCH.Sec8.E

open Circuit

/-! ## The other wires -/

/-- The wires `0, …, n - 1` not in `tg`, increasing. -/
def rest (n : ℕ) (tg : List ℕ) : List ℕ := (List.range n).filter fun j => !(tg.contains j)

section Rest

variable {n : ℕ} {tg : List ℕ}

theorem rest_pairwise : (rest n tg).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_rest {j : ℕ} : j ∈ rest n tg ↔ j < n ∧ j ∉ tg := by
  simp [rest, List.mem_filter, List.mem_range]

theorem rest_length (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < n) : (rest n tg).length + tg.length = n := by
  have e := List.length_eq_length_filter_add (l := List.range n) (fun j => tg.contains j)
  rw [List.length_range] at e
  have hp : ((List.range n).filter fun j => tg.contains j).Perm tg := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hnd]
    intro a
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hlt a h, h⟩
  rw [hp.length_eq] at e
  unfold rest; omega

theorem getD_of_lt {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 = l[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_rest_mem {k : ℕ} (hk : k < (rest n tg).length) : (rest n tg).getD k 0 ∈ rest n tg := by
  rw [getD_of_lt hk]; exact List.getElem_mem hk

theorem getD_rest_lt {k k' : ℕ} (hk : k < k') (hk' : k' < (rest n tg).length) :
    (rest n tg).getD k 0 < (rest n tg).getD k' 0 := by
  rw [getD_of_lt (by omega), getD_of_lt hk']
  exact List.pairwise_iff_getElem.1 rest_pairwise k k' (by omega) hk' hk

end Rest

/-! ## Where the network of `placeG` leaves the other wires -/

section Net

variable {n : ℕ} {tg : List ℕ}

theorem curPos_rest_base (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < n) :
    ∀ k, k < (rest n tg).length →
      curPos (tg ++ rest n tg) tg.length ((rest n tg).getD k 0) = tg.length + k := by
  set r := (rest n tg).length with hr
  set ps := tg ++ rest n tg with hps
  have hnd' : ps.Nodup := by
    rw [hps, List.nodup_append]
    refine ⟨hnd, rest_pairwise.imp (fun h => Nat.ne_of_lt h), fun a ha b hb e => ?_⟩
    subst e; exact (mem_rest.1 hb).2 ha
  have hpsN : ∀ p ∈ ps, p < n := by
    intro p hp
    rcases List.mem_append.1 hp with h | h
    · exact hlt p h
    · exact (mem_rest.1 h).1
  have htake : ps.take tg.length = tg := by simp [hps]
  have hnot : ∀ k, k < r → (rest n tg).getD k 0 ∉ ps.take tg.length := by
    intro k hk; rw [htake]; exact (mem_rest.1 (getD_rest_mem hk)).2
  have hlen := rest_length hnd hlt
  have hle : tg.length ≤ ps.length := by simp [hps]
  -- lower bound
  have lo : ∀ k, k < r → tg.length + k ≤ curPos ps tg.length ((rest n tg).getD k 0) := by
    intro k
    induction k with
    | zero => intro hk; simpa using MS.curPos_ge hnd' hle (hnot 0 hk)
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := MS.curPos_lt hnd' (hnot k (by omega)) (hnot (k + 1) hk)
        (getD_rest_lt (by omega) hk)
      omega
  -- upper bound
  have hi : ∀ d, ∀ k, k + d + 1 = r → curPos ps tg.length ((rest n tg).getD k 0) ≤ tg.length + k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have hq : (rest n tg).getD k 0 < n := (mem_rest.1 (getD_rest_mem (by omega))).1
      have := MS.curPos_le (i := tg.length) hnd' hpsN hq
      omega
    | succ d ih =>
      intro k hk
      have h1 := ih (k + 1) (by omega)
      have h2 := MS.curPos_lt hnd' (hnot k (by omega)) (hnot (k + 1) (by omega))
        (getD_rest_lt (by omega) (by omega))
      omega
  intro k hk
  exact le_antisymm (hi (r - k - 1) k (by omega)) (lo k hk)

theorem curPos_rest (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < n) {k : ℕ}
    (hk : k < (rest n tg).length) :
    curPos (tg ++ rest n tg) (tg.length + k) ((tg ++ rest n tg).getD (tg.length + k) 0) =
      tg.length + k := by
  have hq : (tg ++ rest n tg).getD (tg.length + k) 0 = (rest n tg).getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have hz : ((rest n tg).take k).filter (fun p => decide ((rest n tg).getD k 0 < p)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [List.getElem_take]
    have hik : i < k := by simp at hi; omega
    have := getD_rest_lt (n := n) (tg := tg) hik hk
    rw [getD_of_lt (by omega)] at this
    simp only [decide_eq_true_eq, not_lt]
    exact this.le
  have e : curPos (tg ++ rest n tg) (tg.length + k) ((rest n tg).getD k 0) =
      curPos (tg ++ rest n tg) tg.length ((rest n tg).getD k 0) := by
    rw [MS.curPos_def, MS.curPos_def, List.take_append, List.take_append, Nat.add_sub_cancel_left,
      Nat.sub_self, List.take_zero, List.append_nil,
      List.take_of_length_le (by omega : tg.length ≤ tg.length + k),
      List.take_of_length_le (le_refl _), List.filter_append, List.length_append, hz]
    rfl
  rw [hq, e, curPos_rest_base hnd hlt k hk]

/-- The network of `placeG` at `tg` followed by the other wires is that of `tg`. -/
theorem netPos_rest (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < n) :
    MS.netPos (tg ++ rest n tg) = MS.netPos tg := by
  unfold MS.netPos
  rw [List.length_append, List.range_add, List.flatMap_append]
  have h2 : ((List.range (rest n tg).length).map (tg.length + ·)).flatMap
      (fun i => MS.mvPos (curPos (tg ++ rest n tg) i ((tg ++ rest n tg).getD i 0)) i) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro i hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
    rw [curPos_rest hnd hlt (List.mem_range.1 hk)]
    simp [MS.mvPos]
  rw [h2, List.append_nil]
  apply List.flatMap_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  have e1 : (tg ++ rest n tg).getD i 0 = tg.getD i 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  rw [e1, MS.curPos_def, MS.curPos_def, List.take_append_of_le_length hi'.le]

theorem netL_rest (N : ℕ) (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < n) :
    netL N (tg ++ rest n tg) = netL N tg := by
  rw [MS.netL_eq, MS.netL_eq, netPos_rest hnd hlt]

end Net

/-! ## The decoded multi-controlled `H` -/

theorem range_rev_filter_pos (m : ℕ) :
    (List.range m).reverse.filter (· ≥ 1) = (List.range (m - 1)).reverse.map (1 + ·) := by
  cases m with
  | zero => simp
  | succ m =>
    rw [List.range_succ_eq_map, List.reverse_cons, List.filter_append,
      List.filter_eq_self.2 (by intro a ha; simp at ha; obtain ⟨b, _, rfl⟩ := ha; simp)]
    simp [List.map_reverse, Nat.add_comm 1]

theorem netL_two (N b h : ℕ) :
    netL N [b, h] = down N b ++ down1 N (if h < b then h + 1 else h) := by
  have hc : curPos [b, h] 1 h = if h < b then h + 1 else h := by
    simp only [curPos, List.take_succ_cons, List.take_zero, List.filter_cons, List.filter_nil]
    split_ifs <;> simp_all
  have hn : MS.netPos [b, h] = MS.mvPos (curPos [b, h] 0 b) 0 ++ MS.mvPos (curPos [b, h] 1 h) 1 := by
    simp [MS.netPos, List.range_succ]
  have h0 : curPos [b, h] 0 b = b := by simp [curPos]
  rw [MS.netL_eq, hn, hc, h0, List.map_append]
  congr 1
  · simp [MS.mvPos, down]
  · rw [down1, range_rev_filter_pos]
    simp [MS.mvPos]

/-- The controls of a decoded multi-controlled `H`: on every wire but `u` and
`w`, black where the bit of `s` is `1`, white where it is `0`. -/
def ctl2Of (s u w : ℕ) : ℕ → Option Bool :=
  fun j => if j = u ∨ j = w then none else some (decide (bitOf s j = 1))

theorem ctrlWires_ctl2Of {n : ℕ} (s b h : ℕ) :
    ctrlWires n [b, h] (ctl2Of s b h) = rest n [b, h] := by
  unfold ctrlWires rest
  apply List.filter_congr
  intro j _
  by_cases hj : j = b ∨ j = h
  · have h1 : ctl2Of s b h j = none := if_pos hj
    rcases hj with rfl | rfl <;> simp [h1]
  · have h1 : ctl2Of s b h j = some (decide (bitOf s j = 1)) := if_neg hj
    push Not at hj
    rw [h1]; simp [hj.1, hj.2]

theorem whiteWires_ctl2Of (n s b h : ℕ) :
    whiteWires n [b, h] (ctl2Of s b h) =
      (List.range n).filter fun j => !(j == b || j == h) && bitOf s j == 0 := by
  unfold whiteWires
  apply List.filter_congr
  intro j _
  by_cases hj : j = b ∨ j = h
  · have h1 : ctl2Of s b h j = none := if_pos hj
    rcases hj with rfl | rfl <;> simp [h1]
  · have h1 : ctl2Of s b h j = some (decide (bitOf s j = 1)) := if_neg hj
    push Not at hj
    have h3 := bitOf_lt_two s j
    rw [h1]
    rcases (show bitOf s j = 0 ∨ bitOf s j = 1 by omega) with e | e <;> simp [e, hj.1, hj.2]

theorem ctl2Of_comm (s u w : ℕ) : ctl2Of s u w = ctl2Of s w u := by
  funext j; simp [ctl2Of, or_comm]

/-- The multi-controlled `H` with its box on wire `b` and its `H` on wire `h`,
placed by `placeAt2` and coloured by the bits of `s` (Definition 8.3), is
`mc n .hg [b, h] c`. -/
theorem placeAt2_mc (k s b h : ℕ) (hb : b < k + 2) (hh : h < k + 2) (hbh : b ≠ h) :
    colour (k + 2) (placeAt2 (k + 2) (stdMch (k + 2)) h b) (bitOf s) (fun j => j == b || j == h) =
      mc (k + 2) .hg [b, h] (ctl2Of s b h) := by
  have hnd : [b, h].Nodup := by simp [hbh]
  have hlt : ∀ t ∈ [b, h], t < k + 2 := by simp [hb, hh]
  have hlen := rest_length hnd hlt
  simp only [List.length_cons, List.length_nil] at hlen
  unfold mc colourW
  rw [ctrlWires_ctl2Of, whiteWires_ctl2Of]
  show colour (k + 2) _ _ _ = drawn (_ ++ [placeG (k + 2) (mch (rest (k + 2) [b, h]).length) _] ++ _)
  rw [show (rest (k + 2) [b, h]).length = k by omega]
  unfold placeG colour placeAt2
  rw [netL_rest (k + 2) hnd hlt, netL_two, atBot_self]
  rfl

end QCert.RealCliffordCH.Sec8.E
