/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: the decoded letters as multi-controlled gates

The decoding of Definition 8.3 places the canonical gate on its wire with
the swap network `down t` and colours it with `colour`; in the conventions
of `MC` the same circuit is `mc n K [t] c`, the controls `c` being the bits
of `G_n(a)` on the other wires (`ctlOf`).  These are equalities of circuits
(no derivation): the network `netL` of `placeG` at the wires `t, 0, …, t-1,
t+1, …` is `down t` (`netL_others`).

* `dZZ1_mc`: `D((-1)_[a](-1)_[a+1])` is the box on the wire `t` where
  `G_n(a)` and `G_n(a + 1)` differ, controlled by the other bits of `G_n(a)`.
* `dZX1_mc`: `D((-1)_[a]X_[a,a+1])` and `D((-1)_[a+1]X_[a,a+1])` are the
  multi-controlled `XZ` or `ZX` on that wire.
* `mc_congr`: `mc N K tg c` only depends on `c` below `N`.
-/
import QCert.RealCliffordCH.Sec8.MCSem

namespace QCert.RealCliffordCH.Sec8.E

open Circuit

/-! ## The wires other than `t` -/

/-- The `j`-th wire other than `t`. -/
def skipAt (t j : ℕ) : ℕ := if j < t then j else j + 1

theorem skipAt_strictMono (t : ℕ) : StrictMono (skipAt t) := by
  intro i j h; unfold skipAt; split_ifs <;> omega

/-- The wires of `0, …, n - 1` other than `t`, increasing. -/
theorem filter_ne_range {n t : ℕ} (ht : t < n) :
    (List.range n).filter (fun j => decide (j ≠ t)) = (List.range (n - 1)).map (skipAt t) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge t n with h | h
    · rw [ih h, show n + 1 - 1 = (n - 1) + 1 by omega, List.range_succ, List.map_append]
      have : skipAt t (n - 1) = n := by unfold skipAt; split_ifs <;> omega
      simp [this, show n ≠ t by omega]
    · have htn : t = n := by omega
      subst htn
      rw [List.filter_eq_self.2 (by intro j hj; simp at hj; simp; omega)]
      simp only [List.filter_cons, List.filter_nil, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, if_false, List.append_nil, Nat.add_sub_cancel]
      symm
      rw [List.map_congr_left (g := id) (by intro j hj; simp at hj; simp [skipAt, hj])]
      simp

/-- `netL` at the wires `t, 0, …, t - 1, t + 1, …` is the network `down t`
carrying wire `t` to wire 0. -/
theorem netPos_others {n t : ℕ} (ht : t < n) :
    MS.netPos (t :: (List.range (n - 1)).map (skipAt t)) = (List.range t).reverse := by
  set ps := t :: (List.range (n - 1)).map (skipAt t) with hps
  have hlen : ps.length = (n - 1) + 1 := by simp [hps]
  unfold MS.netPos
  rw [hlen, List.range_succ_eq_map, List.flatMap_cons]
  have h0 : MS.mvPos (curPos ps 0 (ps.getD 0 0)) 0 = (List.range t).reverse := by
    simp [MS.mvPos, curPos, hps]
  rw [h0]
  suffices hrest : ((List.range (n - 1)).map Nat.succ).flatMap
      (fun i => MS.mvPos (curPos ps i (ps.getD i 0)) i) = [] by
    rw [hrest, List.append_nil]
  rw [List.flatMap_eq_nil_iff]
  intro i hi
  simp only [List.mem_map, List.mem_range] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  have hget : ps.getD (j + 1) 0 = skipAt t j := by
    simp [hps, List.getD_eq_getElem?_getD, hj]
  have htake : ps.take (j + 1) = t :: (List.range j).map (skipAt t) := by
    simp only [hps, List.take_succ_cons, ← List.map_take, List.take_range,
      Nat.min_eq_left (show j ≤ n - 1 by omega)]
  have hcur : curPos ps (j + 1) (skipAt t j) = j + 1 := by
    unfold curPos
    rw [htake, List.filter_cons]
    have hf : ((List.range j).map (skipAt t)).filter (fun p => decide (skipAt t j < p)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      simp only [List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      have := skipAt_strictMono t hi
      simp only [decide_eq_true_eq, not_lt]
      exact this.le
    rw [hf]
    by_cases h1 : j < t
    · have e : skipAt t j = j := if_pos h1
      rw [e]; simp [h1]
    · have e : skipAt t j = j + 1 := if_neg h1
      rw [e, if_neg (by simp; omega)]; simp
  rw [Nat.succ_eq_add_one, hget, hcur]
  simp [MS.mvPos]

theorem netL_others (N : ℕ) {n t : ℕ} (ht : t < n) :
    netL N (t :: (List.range (n - 1)).map (skipAt t)) = down N t := by
  rw [MS.netL_eq, netPos_others ht, down]

/-! ## Multi-controlled gates depend on their controls below the width -/

theorem ctrlWires_congr {N : ℕ} {tg : List ℕ} {c c' : ℕ → Option Bool}
    (h : ∀ j < N, c j = c' j) : ctrlWires N tg c = ctrlWires N tg c' := by
  unfold ctrlWires
  apply List.filter_congr
  intro j hj
  rw [h j (List.mem_range.1 hj)]

theorem whiteWires_congr {N : ℕ} {tg : List ℕ} {c c' : ℕ → Option Bool}
    (h : ∀ j < N, c j = c' j) : whiteWires N tg c = whiteWires N tg c' := by
  unfold whiteWires
  apply List.filter_congr
  intro j hj
  rw [h j (List.mem_range.1 hj)]

theorem mc_congr {N : ℕ} {K : Kind} {tg : List ℕ} {c c' : ℕ → Option Bool}
    (h : ∀ j < N, c j = c' j) : mc N K tg c = mc N K tg c' := by
  unfold mc
  rw [ctrlWires_congr h, whiteWires_congr h]

/-! ## The decoded letters -/

/-- The wire where `G_n(a)` and `G_n(a + 1)` differ (Definition 8.3). -/
def tOf (n a : ℕ) : ℕ :=
  ((List.range n).find? fun j => bitOf (gray a) j ≠ bitOf (gray (a + 1)) j).getD 0

/-- The controls of a decoded letter: on every wire but `t`, black where the
bit of `s` is `1`, white where it is `0`. -/
def ctlOf (s t : ℕ) : ℕ → Option Bool := fun j => if j = t then none else some (decide (bitOf s j = 1))

theorem bitOf_lt_two (v i : ℕ) : bitOf v i < 2 := Nat.mod_lt _ (by norm_num)

theorem ctrlWires_ctlOf {n : ℕ} (s t : ℕ) (ht : t < n) :
    ctrlWires n [t] (ctlOf s t) = (List.range (n - 1)).map (skipAt t) := by
  rw [← filter_ne_range ht]
  unfold ctrlWires
  apply List.filter_congr
  intro j _
  by_cases hj : j = t
  · subst hj
    have h1 : ctlOf s j j = none := if_pos rfl
    rw [h1]; simp
  · have h1 : ctlOf s t j = some (decide (bitOf s j = 1)) := if_neg hj
    have h2 : [t].contains j = false := by simpa using hj
    rw [h1, h2]; simp [hj]

theorem whiteWires_ctlOf (n s t : ℕ) :
    whiteWires n [t] (ctlOf s t) =
      (List.range n).filter fun j => !(j == t) && bitOf s j == 0 := by
  unfold whiteWires
  apply List.filter_congr
  intro j _
  by_cases hj : j = t
  · subst hj
    have h1 : ctlOf s j j = none := if_pos rfl
    rw [h1]; simp
  · have h1 : ctlOf s t j = some (decide (bitOf s j = 1)) := if_neg hj
    have h2 : [t].contains j = false := by simpa using hj
    have h3 := bitOf_lt_two s j
    rw [h1, h2]
    rcases (show bitOf s j = 0 ∨ bitOf s j = 1 by omega) with h | h <;> simp [h, hj]

theorem tOf_lt {n : ℕ} (a : ℕ) (hn : 0 < n) : tOf n a < n := by
  unfold tOf
  cases h : (List.range n).find? (fun j => bitOf (gray a) j ≠ bitOf (gray (a + 1)) j) with
  | none => simpa using hn
  | some j => simpa using List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- A circuit on all `k + 1` wires moved to wire `t` by `placeAt` is the
circuit placed by `placeG` on `t` and the other wires in increasing order. -/
theorem placeG_others {k t : ℕ} (ht : t < k + 1) (g : Circ (k + 1)) :
    placeG (k + 1) g (t :: (List.range k).map (skipAt t)) = placeAt (k + 1) g t := by
  have e := netL_others (k + 1) (n := k + 1) ht
  simp only [Nat.add_sub_cancel] at e
  unfold placeG placeAt
  rw [e, atBot_self]

/-- `D((-1)_[a](-1)_[a+1])` (Definition 8.3) is the box on the wire `t` where
`G_n(a)` and `G_n(a + 1)` differ, controlled by the other bits of `G_n(a)`. -/
theorem dZZ1_mc (k a : ℕ) :
    dZZ1 (k + 1) a = mc (k + 1) .box [tOf (k + 1) a] (ctlOf (gray a) (tOf (k + 1) a)) := by
  have ht := tOf_lt (n := k + 1) a (by omega)
  unfold mc colourW
  rw [ctrlWires_ctlOf _ _ ht, whiteWires_ctlOf]
  simp only [Nat.add_sub_cancel, List.length_map, List.length_range, List.singleton_append]
  show colour (k + 1) (placeAt (k + 1) (box k) (tOf (k + 1) a)) (bitOf (gray a))
      (· == tOf (k + 1) a) = _
  rw [← placeG_others ht]
  rfl

/-- The kind of `D((-1)_[a]X_[a,a+1])` (`which = 0`) and `D((-1)_[a+1]X_[a,a+1])`
(`which = 1`): `XZ` or `ZX` according to `which` and the bit of `G_n(a)` on
the wire `t`. -/
def kindZX (n a which : ℕ) : Kind :=
  if (which = 0) = (bitOf (gray a) (tOf n a) = 0) then .xz else .zx

/-- `D((-1)_[a]X_[a,a+1])` and `D((-1)_[a+1]X_[a,a+1])` (Definition 8.3) are the
multi-controlled `XZ` or `ZX` on the wire `t` where `G_n(a)` and `G_n(a + 1)`
differ, controlled by the other bits of `G_n(a)`. -/
theorem dZX1_mc (k a which : ℕ) :
    dZX1 (k + 1) a which =
      mc (k + 1) (kindZX (k + 1) a which) [tOf (k + 1) a] (ctlOf (gray a) (tOf (k + 1) a)) := by
  have ht := tOf_lt (n := k + 1) a (by omega)
  unfold mc colourW kindZX
  rw [ctrlWires_ctlOf _ _ ht, whiteWires_ctlOf]
  simp only [Nat.add_sub_cancel, List.length_map, List.length_range, List.singleton_append]
  by_cases hw : (which = 0) = (bitOf (gray a) (tOf (k + 1) a) = 0)
  · rw [if_pos hw]
    show colour (k + 1) (placeAt (k + 1) (if (which = 0) = (bitOf (gray a) (tOf (k + 1) a) = 0)
      then xz k else zx k) (tOf (k + 1) a)) (bitOf (gray a)) (· == tOf (k + 1) a) = _
    rw [if_pos hw, ← placeG_others ht]
    rfl
  · rw [if_neg hw]
    show colour (k + 1) (placeAt (k + 1) (if (which = 0) = (bitOf (gray a) (tOf (k + 1) a) = 0)
      then xz k else zx k) (tOf (k + 1) a)) (bitOf (gray a)) (· == tOf (k + 1) a) = _
    rw [if_neg hw, ← placeG_others ht]
    rfl

end QCert.RealCliffordCH.Sec8.E
