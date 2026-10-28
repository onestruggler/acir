/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# States after a word, transfers, and entries outside a window

* `state_after`: if the scaled action of a word `K` on the numerators of
  `s`, divided by `√2 ^ (number of H in K)`, is integral with an odd entry,
  then `K s` has the pivot and the exponent of `s`, and these are its
  numerators.  On a window with a pattern (`pat_after`), the new window has
  the pattern `divAll P K`, computed by evaluation, and the entries outside
  the window are unchanged.
* `Join.transfer_gen`: a join at `K s` gives one at `s`, if `K` commutes with
  the two words, does not raise the level of `s`, and keeps the states of
  `K` from `A s` and `B s` below `s` (Clément's Lemma 5.3).
* `tail_entry`, `tail_odd_entry`, `tail_class_even`: Clément's Lemma 2.1 on
  a state reached by a word on a window, read off its pattern.
-/
import QCert.HadamardPi.Sym

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### The state after a word -/

theorem below_of_idx {s : O n} {K : List (Gen n)} (hK : ∀ g ∈ K, ∀ i ∈ g.idx, (i : ℕ) < piv s) :
    Below (piv s) (ofList K) := by
  intro g hg; exact hK g (by simpa using hg)

theorem pj_eq_of_piv {s s' : O n} (hs : s ≠ 1) (hs' : s' ≠ 1) (h : piv s' = piv s) :
    pj s' (piv_pos hs') = pj s (piv_pos hs) := Fin.ext (by rw [pj_val, pj_val, h])

/-- Numerators after a word, given at the old exponent with an odd one. -/
theorem state_after {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {K : List (Gen n)} (hK : ∀ g ∈ K, ∀ i ∈ g.idx, (i : ℕ) < piv s) {U : Fin n → ℤ√2}
    (hU : ∀ i, rt2 ^ hcntw K * U i = scw K (num (col s (pj s (piv_pos hs)))) i)
    {i0 : Fin n} (hodd : Odd (U i0).re) :
    ∃ hs' : run K s ≠ 1, piv (run K s) = piv s ∧
      lde (col (run K s) (pj _ (piv_pos hs'))) = lde (col s (pj s (piv_pos hs))) ∧
      ∀ i, num (col (run K s) (pj _ (piv_pos hs'))) i = U i := by
  classical
  have hp := piv_pos hs
  set v := col s (pj s hp) with hv
  set k := lde v with hkdef
  have hR : InRing v := col_inRing s _
  have hcol : col (run K s) (pj s hp) = wv (ofList K) v := by
    rw [run_eq_lift]; exact col_lift_mul' _ _ _
  have hsc := toReal_scw K (U := num v) (x := v) (K := k) (toReal_num hR)
  have hU' : ∀ i, toReal (U i) = Real.sqrt 2 ^ k * col (run K s) (pj s hp) i := by
    intro i
    have e := hsc i
    rw [← hU i, map_mul, map_pow, toReal_rt2, ← hcol] at e
    exact cancel_sqrt2_pow e
  have hR' : InRing (col (run K s) (pj s hp)) := col_inRing _ _
  have hle : lde (col (run K s) (pj s hp)) ≤ k := lde_le fun i => ⟨U i, hU' i⟩
  have hge : k ≤ lde (col (run K s) (pj s hp)) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨K', hK'⟩ : ∃ K', k = K' + 1 := ⟨k - 1, by omega⟩
    have hd : Den K' (col (run K s) (pj s hp) i0) := ((denV_lde hR').mono (by omega)) i0
    have e := hU' i0
    rw [hK'] at e
    exact not_den_of_odd e hodd hd
  have hpiv : piv (run K s) = piv s := by
    apply le_antisymm
    · rw [run_eq_lift]; exact piv_le_of_below (below_of_idx hK)
    · by_contra hlt
      push Not at hlt
      have hf : Fixed (run K s) (pj s hp) := fixed_of_piv_le (by rw [pj_val]; omega)
      have h0 : lde (col (run K s) (pj s hp)) = 0 := by
        rw [show col (run K s) (pj s hp) = Pi.single (pj s hp) 1 from hf]
        exact lde_single (Or.inl rfl)
      omega
  have hs' : run K s ≠ 1 := fun h => by
    have := piv_eq_zero_iff.2 h; omega
  have e := pj_eq_of_piv hs hs' hpiv
  refine ⟨hs', hpiv, ?_, ?_⟩
  · rw [e]; exact le_antisymm hle hge
  · intro i
    rw [e]
    exact congrFun (num_eq hR' (by rw [le_antisymm hle hge]; exact hU')) i

/-! ### On a window -/

/-- The window after a word, at the old exponent. -/
def divAll {w : ℕ} (P : List ZL) (K : List (Gen w)) : List ZL :=
  (List.range w).map fun j => (divAt P K j).getD dZ

/-- Every entry of the window after the word is integral. -/
def allSome {w : ℕ} (P : List ZL) (K : List (Gen w)) : Bool :=
  (List.range w).all fun j => (divAt P K j).isSome

theorem divAll_getD {w : ℕ} (P : List ZL) (K : List (Gen w)) (j : Fin w) :
    (divAll P K).getD j dZ = (divAt P K j).getD dZ := by
  simp [divAll, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2]

theorem divAll_sound {w : ℕ} {P : List ZL} {K : List (Gen w)} (hc : allSome P K = true)
    (t : ℕ → ℤ) (j : Fin w) :
    rt2 ^ hcntw K * zev ((divAll P K).getD j dZ) t = scw K (pv P t) j := by
  have : (divAt P K j).isSome = true := by
    simp only [allSome, List.all_eq_true, List.mem_range] at hc; exact hc j j.2
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
  rw [divAll_getD, hy, Option.getD_some, zdivp_sound _ hy t, scwL_sound]

theorem scw_window {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) (K : List (Gen w))
    (V : Fin n → ℤ√2) (j : Fin w) :
    scw (K.map (Gen.map f hf)) V (f j) = scw K (V ∘ f) j := scw_map f hf K V j

theorem scw_tail {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) (K : List (Gen w))
    (V : Fin n → ℤ√2) {i : Fin n} (hi : ∀ j, f j ≠ i) :
    scw (K.map (Gen.map f hf)) V i = rt2 ^ hcntw K * V i := by
  rw [scw_out _ V i, hcntw_map]
  intro g hg hig
  rw [List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  obtain ⟨j, hj⟩ := idx_map f hf g0 hig
  exact hi j hj

/-- The state after a word on a window with a pattern. -/
theorem pat_after {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (K : List (Gen w)) (hc : allSome P K = true) (j0 : Fin w)
    (ho : oddSure ((divAll P K).getD j0 dZ) = true) :
    ∃ hs' : run (K.map (Gen.map f hf)) s ≠ 1, piv (run (K.map (Gen.map f hf)) s) = piv s ∧
      lde (col (run (K.map (Gen.map f hf)) s) (pj _ (piv_pos hs'))) =
        lde (col s (pj s (piv_pos hs))) ∧
      (∀ j : Fin w, num (col (run (K.map (Gen.map f hf)) s) (pj _ (piv_pos hs'))) (f j) =
        zev ((divAll P K).getD j dZ) t) ∧
      ∀ i, (∀ j, f j ≠ i) →
        num (col (run (K.map (Gen.map f hf)) s) (pj _ (piv_pos hs'))) i =
          num (col s (pj s (piv_pos hs))) i := by
  classical
  set v := col s (pj s (piv_pos hs))
  let U : Fin n → ℤ√2 := fun i =>
    if h : ∃ j, f j = i then zev ((divAll P K).getD h.choose dZ) t else num v i
  have hUf : ∀ j, U (f j) = zev ((divAll P K).getD j dZ) t := by
    intro j
    have h : ∃ j', f j' = f j := ⟨j, rfl⟩
    simp only [U, dif_pos h]
    rw [hf.injective h.choose_spec]
  have hUt : ∀ i, (∀ j, f j ≠ i) → U i = num v i := by
    intro i hi
    have h : ¬∃ j, f j = i := fun ⟨j, hj⟩ => hi j hj
    simp only [U, dif_neg h]
  have hpv : (num v ∘ f) = pv P t := funext hP
  have hK : ∀ g ∈ K.map (Gen.map f hf), ∀ i ∈ g.idx, (i : ℕ) < piv s := by
    intro g hg i hi
    rw [List.mem_map] at hg
    obtain ⟨g0, -, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := idx_map f hf g0 hi
    exact hfJ j
  have hU : ∀ i, rt2 ^ hcntw (K.map (Gen.map f hf)) * U i =
      scw (K.map (Gen.map f hf)) (num v) i := by
    intro i
    rw [hcntw_map]
    by_cases h : ∃ j, f j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hUf, scw_window, hpv, divAll_sound hc]
    · have hi : ∀ j, f j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [hUt i hi, scw_tail f hf K _ hi]
  have hodd : Odd (U (f j0)).re := by rw [hUf]; exact odd_of_oddSure ho t
  obtain ⟨hs', hpiv, hl, hnum⟩ := state_after hs hk hK hU hodd
  exact ⟨hs', hpiv, hl, fun j => by rw [hnum, hUf], fun i hi => by rw [hnum, hUt i hi]⟩

/-! ### Levels -/

theorem lev_eq_of_num {s s' : O n} (hs : s ≠ 1) (hs' : s' ≠ 1) (hpiv : piv s' = piv s)
    (hl : lde (col s' (pj s' (piv_pos hs'))) = lde (col s (pj s (piv_pos hs))))
    (ho : ∀ i, Odd (num (col s' (pj s' (piv_pos hs'))) i).re ↔
      Odd (num (col s (pj s (piv_pos hs))) i).re) : lev s' = lev s := by
  have hoS : oddSet (col s' (pj s' (piv_pos hs'))) = oddSet (col s (pj s (piv_pos hs))) := by
    ext i; rw [mem_oddSet, mem_oddSet]; exact ho i
  rw [lev, lev, hpiv, pcol_eq (piv_pos hs'), pcol_eq (piv_pos hs), kl_eq_of hl hoS]

/-- The window has the same odd entries before and after. -/
def sameOdd {w : ℕ} (P P' : List ZL) : Bool :=
  (List.range w).all fun j =>
    (oddSure (P.getD j dZ) && oddSure (P'.getD j dZ)) ||
      (allEven (P.getD j dZ).1 && allEven (P'.getD j dZ).1)

theorem sameOdd_iff {w : ℕ} {P P' : List ZL} (h : sameOdd (w := w) P P' = true) (t : ℕ → ℤ)
    (j : Fin w) : Odd (zev (P'.getD j dZ) t).re ↔ Odd (zev (P.getD j dZ) t).re := by
  simp only [sameOdd, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h j j.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact iff_of_true (odd_of_oddSure h2 t) (odd_of_oddSure h1 t)
  · exact iff_of_false (not_odd_of_allEven h2 t) (not_odd_of_allEven h1 t)

/-- A word on a window with a pattern that keeps the odd entries keeps the
level. -/
theorem lev_after_eq {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) (hfJ : ∀ j, (f j : ℕ) < piv s) {P : List ZL}
    {t : ℕ → ℤ} (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (K : List (Gen w)) (hc : allSome P K = true) (j0 : Fin w)
    (ho : oddSure ((divAll P K).getD j0 dZ) = true) (hsame : sameOdd (w := w) P (divAll P K) = true) :
    lev (run (K.map (Gen.map f hf)) s) = lev s := by
  classical
  obtain ⟨hs', hpiv, hl, hwin, htail⟩ := pat_after f hf hs hk hfJ hP K hc j0 ho
  refine lev_eq_of_num hs hs' hpiv hl fun i => ?_
  by_cases h : ∃ j, f j = i
  · obtain ⟨j, rfl⟩ := h
    rw [hwin, hP]; exact sameOdd_iff hsame t j
  · rw [htail i fun j hj => h ⟨j, hj⟩]

/-! ### Entries outside a window -/

/-- The entry `j` of the window after `K`, `δ` below the old exponent. -/
def divAtD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ j : ℕ) : Option ZL :=
  zdivp (hcntw K + δ) ((scwL K P).getD j dZ)

def divAllD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ : ℕ) : List ZL :=
  (List.range w).map fun j => (divAtD P K δ j).getD dZ

def allSomeD {w : ℕ} (P : List ZL) (K : List (Gen w)) (δ : ℕ) : Bool :=
  (List.range w).all fun j => (divAtD P K δ j).isSome

theorem divAllD_sound {w : ℕ} {P : List ZL} {K : List (Gen w)} {δ : ℕ}
    (hc : allSomeD P K δ = true) (t : ℕ → ℤ) (j : Fin w) :
    rt2 ^ (hcntw K + δ) * zev ((divAllD P K δ).getD j dZ) t = scw K (pv P t) j := by
  have : (divAtD P K δ j).isSome = true := by
    simp only [allSomeD, List.all_eq_true, List.mem_range] at hc; exact hc j j.2
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
  have e : (divAllD P K δ).getD j dZ = (divAtD P K δ j).getD dZ := by
    simp [divAllD, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [e, hy, Option.getD_some, zdivp_sound _ hy t, scwL_sound]

/-- The numerators of the state `D s` at `δ` below the exponent of `s`, when
the entries outside the window are divisible by `√2 ^ δ`. -/
theorem tail_numerators {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (D : List (Gen w)) (δ : ℕ) (hδ : δ ≤ lde (col s (pj s (piv_pos hs))))
    (hc : allSomeD P D δ = true)
    (htail : ∀ i, (∀ j, f j ≠ i) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i) :
    ∃ U : Fin n → ℤ√2, (∀ i, toReal (U i) = Real.sqrt 2 ^ (lde (col s (pj s (piv_pos hs))) - δ) *
        col (run (D.map (Gen.map f hf)) s) (pj s (piv_pos hs)) i) ∧
      (∀ j, U (f j) = zev ((divAllD P D δ).getD j dZ) t) ∧
      ∀ i, (∀ j, f j ≠ i) → rt2 ^ δ * U i = num (col s (pj s (piv_pos hs))) i := by
  classical
  set v := col s (pj s (piv_pos hs))
  set k := lde v
  have hR : InRing v := col_inRing s _
  let U : Fin n → ℤ√2 := fun i =>
    if h : ∃ j, f j = i then zev ((divAllD P D δ).getD h.choose dZ) t
    else if h' : ∀ j, f j ≠ i then (htail i h').choose else 0
  have hUf : ∀ j, U (f j) = zev ((divAllD P D δ).getD j dZ) t := by
    intro j
    have h : ∃ j', f j' = f j := ⟨j, rfl⟩
    simp only [U, dif_pos h]
    rw [hf.injective h.choose_spec]
  have hUt : ∀ i, (∀ j, f j ≠ i) → rt2 ^ δ * U i = num v i := by
    intro i hi
    have h : ¬∃ j, f j = i := fun ⟨j, hj⟩ => hi j hj
    simp only [U, dif_neg h, dif_pos hi]
    exact (htail i hi).choose_spec
  have hpv : (num v ∘ f) = pv P t := funext hP
  have hcol : col (run (D.map (Gen.map f hf)) s) (pj s (piv_pos hs)) =
      wv (ofList (D.map (Gen.map f hf))) v := by
    rw [run_eq_lift]; exact col_lift_mul' _ _ _
  have hsc := toReal_scw (D.map (Gen.map f hf)) (U := num v) (x := v) (K := k) (toReal_num hR)
  refine ⟨U, fun i => ?_, hUf, hUt⟩
  have e := hsc i
  rw [← hcol, hcntw_map] at e
  have key : rt2 ^ (hcntw D + δ) * U i = scw (D.map (Gen.map f hf)) (num v) i := by
    by_cases h : ∃ j, f j = i
    · obtain ⟨j, rfl⟩ := h
      rw [hUf, scw_window, hpv, divAllD_sound hc]
    · have hi : ∀ j, f j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [scw_tail f hf D _ hi, ← hUt i hi, pow_add]; ring
  rw [← key, map_mul, map_pow, toReal_rt2] at e
  have hk' : k = (k - δ) + δ := by omega
  rw [hk', show k - δ + δ + hcntw D = (k - δ) + (hcntw D + δ) by omega] at e
  exact cancel_sqrt2_pow e

/-- Odd with a constant: the constant odd and the other coefficients even. -/
def oddSureL : List ℤ → Bool
  | [] => false
  | c :: cs => c % 2 == 1 && allEven cs

theorem odd_of_oddSureL {l : List ℤ} (h : oddSureL l = true) (t : ℕ → ℤ) : Odd (evv l (c1 t)) := by
  cases l with
  | nil => simp [oddSureL] at h
  | cons c cs =>
    simp only [oddSureL, Bool.and_eq_true, beq_iff_eq] at h
    rw [evv_c1]
    obtain ⟨m, hm⟩ := even_evv cs t h.2
    exact ⟨c / 2 + m, by rw [hm]; omega⟩

/-- Surely odd of the class `γ` (the parity of the `√2` part). -/
def isCls (γ : Bool) (x : ZL) : Bool := oddSure x && (if γ then oddSureL x.2 else allEven x.2)

/-- Surely not odd of the class `γ`. -/
def notCls (γ : Bool) (x : ZL) : Bool :=
  allEven x.1 || (oddSure x && (if γ then allEven x.2 else oddSureL x.2))

theorem isCls_iff {γ : Bool} {x : ZL} (h : (isCls γ x || notCls γ x) = true) (t : ℕ → ℤ) :
    (Odd (zev x t).re ∧ (Odd (zev x t).im ↔ γ = true)) ↔ isCls γ x = true := by
  have hre := fun h => odd_of_oddSure (x := x) h t
  have hev := fun h => not_odd_of_allEven (x := x) h t
  have him1 : oddSureL x.2 = true → Odd (zev x t).im := fun h => odd_of_oddSureL h t
  have him0 : allEven x.2 = true → ¬Odd (zev x t).im := fun h => by
    rw [Int.not_odd_iff_even]; exact even_evv _ _ h
  by_cases hi : isCls γ x = true
  · rw [iff_true_right hi]
    simp only [isCls, Bool.and_eq_true] at hi
    refine ⟨hre hi.1, ?_⟩
    cases γ <;> simp only [Bool.false_eq_true, if_false, if_true] at hi
    · simp [him0 hi.2]
    · simp [him1 hi.2]
  · rw [iff_false_right hi]
    simp only [hi, Bool.false_or, notCls, Bool.or_eq_true, Bool.and_eq_true] at h
    rintro ⟨a, b⟩
    rcases h with h | ⟨-, h2⟩
    · exact hev h a
    · cases γ
      · simp only [Bool.false_eq_true, if_false, iff_false] at h2 b
        exact b (him1 h2)
      · simp only [if_true, iff_true] at h2 b
        exact him0 h2 b

/-- Every entry has a sure status, and the class `γ` has a count of parity
`par`. -/
def clsCount {w : ℕ} (V : List ZL) (γ : Bool) (par : ℕ) : Bool :=
  (List.range w).all (fun j => isCls γ (V.getD j dZ) || notCls γ (V.getD j dZ)) &&
    (List.range w).countP (fun j => isCls γ (V.getD j dZ)) % 2 == par

theorem card_cls {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {U : Fin n → ℤ√2}
    {V : List ZL} {t : ℕ → ℤ} (hU : ∀ j, U (f j) = zev (V.getD j dZ) t) {γ : Bool} {par : ℕ}
    (hc : clsCount (w := w) V γ par = true) :
    ((univ.map ⟨f, hf.injective⟩).filter fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)).card
      % 2 = par := by
  classical
  simp only [clsCount, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  obtain ⟨hall, hcnt⟩ := hc
  rw [Finset.filter_map, Finset.card_map]
  have : (univ.filter ((fun i => Odd (U i).re ∧ (Odd (U i).im ↔ γ = true)) ∘
      (⟨f, hf.injective⟩ : Fin w ↪ Fin n))) =
      univ.filter fun j : Fin w => isCls γ (V.getD j dZ) = true := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Function.comp, Function.Embedding.coeFn_mk, hU]
    exact isCls_iff (hall j j.2) t
  rw [this, card_filter_univ_fin (fun j => isCls γ (V.getD j dZ))]
  exact hcnt

/-- An entry outside the window forced by an odd class count. -/
theorem tail_entry {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {s : O n} (hs : s ≠ 1)
    {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (f j) = zev (P.getD j dZ) t)
    (D : List (Gen w)) (δ : ℕ) (hδ : δ + 1 ≤ lde (col s (pj s (piv_pos hs))))
    (hc : allSomeD P D δ = true)
    (htail : ∀ i, (∀ j, f j ≠ i) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i)
    (γ : Bool) (hcls : clsCount (w := w) (divAllD P D δ) γ 1 = true) :
    ∃ i, (∀ j, f j ≠ i) ∧ ∃ y, Odd y.re ∧ (Odd y.im ↔ γ = true) ∧
      rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i := by
  classical
  obtain ⟨U, hU, hUf, hUt⟩ := tail_numerators f hf hs hP D δ (by omega) hc htail
  have hW : ∀ g ∈ D.map (Gen.map f hf), ∀ i ∈ g.idx, i ∈ univ.map ⟨f, hf.injective⟩ := by
    intro g hg i hi
    rw [List.mem_map] at hg
    obtain ⟨g0, -, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := idx_map f hf g0 hi
    exact Finset.mem_map_of_mem _ (mem_univ j)
  have hodd := card_cls f hf hUf hcls
  obtain ⟨i, hiW, ho, hcl, he⟩ := exists_tail_entry hs (univ.map ⟨f, hf.injective⟩) hW
    (K := lde (col s (pj s (piv_pos hs))) - δ) (δ := δ) (by omega) (by omega) U hU γ
    (Nat.odd_iff.2 hodd)
  refine ⟨i, fun j hj => hiW (by rw [← hj]; exact Finset.mem_map_of_mem _ (mem_univ j)),
    U i, ho, hcl, he⟩

/-! ### The general transfer -/

/-- A join at `K s` gives one at `s` (Clément's Lemma 5.3). -/
theorem Join.transfer_gen {s : O n} {K A B : List (Gen n)} (hle : lev (run K s) ≤ lev s)
    (hA : Derivable Fig6 (ofList (A ++ K)) (ofList (K ++ A)))
    (hB : Derivable Fig6 (ofList (B ++ K)) (ofList (K ++ B)))
    (pA : PathLt (lev s) K (run A s)) (pB : PathLt (lev s) K (run B s))
    (hJ : Join (run K s) A B) : Join s A B := by
  obtain ⟨D, hD, hP⟩ := hJ
  refine ⟨K.reverse ++ D ++ K, ?_, ?_⟩
  · -- `Kʳ D K A ≈ Kʳ D A K ≈ Kʳ B K ≈ Kʳ K B ≈ B`
    have e1 : K.reverse ++ D ++ K ++ A = K.reverse ++ D ++ (K ++ A) := by simp
    rw [e1, ofList_append]
    refine ((Derivable.refl _).mul hA.symm).trans ?_
    rw [← ofList_append, show K.reverse ++ D ++ (A ++ K) = K.reverse ++ (D ++ A) ++ K by simp,
      ofList_append, ofList_append]
    refine (((Derivable.refl _).mul hD).mul (Derivable.refl _)).trans ?_
    rw [← ofList_append, ← ofList_append, List.append_assoc, ofList_append]
    refine ((Derivable.refl _).mul hB).trans ?_
    rw [← ofList_append, ← List.append_assoc, ofList_append]
    simpa using (rev_cancel K).mul (Derivable.refl (ofList B))
  · have e2 : run K (run A s) = run A (run K s) := by
      rw [← run_append, ← run_append]; exact run_eq_of_der hA.symm s
    have e3 : run D (run A (run K s)) = run K (run B s) := by
      rw [← run_append, run_eq_of_der hD, ← run_append, ← run_append]
      exact run_eq_of_der hB s
    rw [PathLt.append, PathLt.append]
    refine ⟨pA, by rw [e2]; exact hP.mono hle, ?_⟩
    rw [e2, e3]
    exact pB.reverse

end QCert.HadamardPi
