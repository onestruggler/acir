/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The pivot column along a word

The level and the syllable of a state are functions of its pivot index and
its pivot column.  A word whose generators lie below the pivot index of `U`
keeps the later columns and acts on the pivot column by the column action
`gact` of its generators (`pcol_word`), unless it makes it `e_j`, when the
pivot index drops (`pivot_word_lt`).  At a scale `k`, `IsCol v k u` says
that `2^k v` is the integer vector `u`; the generators act on `u` by
integer operations (`isCol_neg`, `isCol_x`, `isCol_k`), and `lde`, the odd
entries and the syllable are read off `u` (`lde_eq`, `oddS_eq`,
`firstOdd_eq`, `syll_eq_pos`).
-/
import QCert.LiRossSelinger.Decomp
import QCert.LiRossSelinger.Square

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-! ## The column action -/

/-- The column `c` of a matrix. -/
def colv (M : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) : Fin n → ℝ := fun r => M r c

/-- The action of a generator on a column. -/
noncomputable def gact : Gen n → (Fin n → ℝ) → (Fin n → ℝ)
  | .neg a, v => fun r => if r = a then -v r else v r
  | .x a b _, v => fun r => v (Equiv.swap a b r)
  | .k a b c d _ _ _, v => fun r =>
      if r = a then (v a + v b + v c + v d) / 2
      else if r = b then (v a - v b + v c - v d) / 2
      else if r = c then (v a + v b - v c - v d) / 2
      else if r = d then (v a - v b - v c + v d) / 2
      else v r

theorem colv_mul (g : Gen n) (M : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    colv (genMat g * M) c = gact g (colv M c) := by
  funext r
  cases g with
  | neg a => exact genMat_neg_mul a M r c
  | x a b h => exact genMat_x_mul_swap h M r c
  | k a b c' d h₁ h₂ h₃ => exact genMat_k_mul h₁ h₂ h₃ M r c

/-- The action of a word (rightmost letter first). -/
noncomputable def wact (l : List (Gen n)) (v : Fin n → ℝ) : Fin n → ℝ := l.foldr gact v

theorem wact_nil (v : Fin n → ℝ) : wact [] v = v := rfl

theorem wact_cons (g : Gen n) (l : List (Gen n)) (v : Fin n → ℝ) :
    wact (g :: l) v = gact g (wact l v) := rfl

theorem colv_word (l : List (Gen n)) (M : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    colv ((l.map genMat).prod * M) c = wact l (colv M c) := by
  induction l with
  | nil => simp [wact]
  | cons g l ih => rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, colv_mul, ih]; rfl

/-! ## Words below the pivot -/

/-- Every generator of `l` lies below the index `j`. -/
def BelowJ (j : ℕ) (l : List (Gen n)) : Prop := ∀ g ∈ l, extent g < j

theorem avoids_of_extent {g : Gen n} {i : Fin n} (h : extent g < i.val) : Avoids g i := by
  cases g with
  | neg a => exact fun e => by subst e; exact absurd h (lt_irrefl _)
  | x a b hab =>
    have := Fin.lt_def.1 hab
    exact ⟨fun e => by subst e; simp [extent] at h; omega, fun e => by subst e; simp [extent] at h⟩
  | k a b c d h₁ h₂ h₃ =>
    have := Fin.lt_def.1 h₁; have := Fin.lt_def.1 h₂; have := Fin.lt_def.1 h₃
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
      simp [extent] at h <;> omega

theorem fixCols_word (U : O_ZHalf n) (l : List (Gen n)) (hl : BelowJ (pivotJ U) l) :
    FixCols (mat (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U)) (pivotJ U) := by
  intro i hi r
  rw [mat_word]
  exact col_unit_of_avoid l (mat U) i (fixCols_pivotJ U i hi)
    (fun g hg => avoids_of_extent (lt_of_lt_of_le (hl g hg) hi)) r

theorem colv_pidx (U : O_ZHalf n) (hU : 0 < pivotJ U) : colv (mat U) (pidx U hU) = pcol U :=
  funext fun r => (pcol_eq U hU r).symm

/-- The unit column `e_j` at the pivot index. -/
def IsUnitAt (v : Fin n → ℝ) (p : Fin n) : Prop := ∀ r, v r = if r = p then 1 else 0

/-- A word below the pivot keeps the pivot index and acts on the pivot column,
unless it makes the column `e_j`. -/
theorem pcol_word (U : O_ZHalf n) (hU : 0 < pivotJ U) (l : List (Gen n))
    (hl : BelowJ (pivotJ U) l) (hne : ¬ IsUnitAt (wact l (pcol U)) (pidx U hU)) :
    pivotJ (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U) = pivotJ U ∧
      pcol (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U) = wact l (pcol U) := by
  set V := FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U
  have hfix := fixCols_word U l hl
  have hcol : colv (mat V) (pidx U hU) = wact l (pcol U) := by
    rw [mat_word, colv_word, colv_pidx]
  have hV : pivotJ V = pivotJ U := by
    rcases Nat.lt_or_eq_of_le (pivotJ_le_of V hfix) with hlt | heq
    · exfalso; apply hne
      intro r
      have hfix' : FixCols (mat V) (pivotJ U - 1) := fun i hi =>
        fixCols_pivotJ V i (by omega)
      have := hfix' (pidx U hU) (by simp [pidx_val]) r
      rw [← hcol]; exact this
    · exact heq
  refine ⟨hV, funext fun r => ?_⟩
  rw [pivot_same hU hfix hV r, ← hcol]; rfl

theorem pivot_word_lt (U : O_ZHalf n) (hU : 0 < pivotJ U) (l : List (Gen n))
    (hl : BelowJ (pivotJ U) l) (heq : IsUnitAt (wact l (pcol U)) (pidx U hU)) :
    pivotJ (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U) < pivotJ U := by
  set V := FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U
  have hfix := fixCols_word U l hl
  have hcol : colv (mat V) (pidx U hU) = wact l (pcol U) := by
    rw [mat_word, colv_word, colv_pidx]
  have hJ : pivotJ U - 1 < n := (pidx U hU).2
  have hfix1 : FixCols (mat V) (pivotJ U - 1 + 1) := by rwa [Nat.sub_add_cancel hU]
  have := fixCols_of_col (mat V) hJ hfix1 (fun r => by
    have h := heq r
    rw [← hcol] at h
    exact h)
  have := pivotJ_le_of V this
  omega

theorem level_eq_mk (V : O_ZHalf n) (hV : 0 < pivotJ V) :
    level V = mkLevel (pivotJ V) (lde V) (nodd V) := by
  unfold level; rw [if_neg (by omega)]

/-! ## Integer columns -/

/-- `2^k v` is the integer vector `u`. -/
def IsCol (v : Fin n → ℝ) (k : ℕ) (u : Fin n → ℤ) : Prop := ∀ r, (2 : ℝ) ^ k * v r = u r

theorem isCol_pcol (U : O_ZHalf n) : IsCol (pcol U) (lde U) (wint U) := wint_spec U

theorem IsCol.intAt {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v k u) : IntAt v k :=
  fun r => ⟨u r, h r⟩

theorem isCol_neg {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v k u) (a : Fin n) :
    IsCol (gact (.neg a) v) k (fun r => if r = a then -u r else u r) := by
  intro r; simp only [gact]
  split_ifs
  · rw [mul_neg, h r]; push_cast; ring
  · exact h r

theorem isCol_x {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v k u) {a b : Fin n}
    (hab : a < b) : IsCol (gact (.x a b hab) v) k (fun r => u (Equiv.swap a b r)) :=
  fun _ => h _

theorem half_cast {e : ℤ} (he : 2 ∣ e) : ((e / 2 : ℤ) : ℝ) = (e : ℝ) / 2 := by
  have : e / 2 * 2 = e := Int.ediv_mul_cancel he
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
  exact_mod_cast this

/-- `K` on four entries whose sum is even keeps the scale. -/
theorem isCol_k {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v k u) {a b c d : Fin n}
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (hev : 2 ∣ u a + u b + u c + u d) :
    IsCol (gact (.k a b c d h₁ h₂ h₃) v) k (fun r =>
      if r = a then (u a + u b + u c + u d) / 2
      else if r = b then (u a - u b + u c - u d) / 2
      else if r = c then (u a + u b - u c - u d) / 2
      else if r = d then (u a - u b - u c + u d) / 2
      else u r) := by
  have e1 : 2 ∣ u a - u b + u c - u d := by omega
  have e2 : 2 ∣ u a + u b - u c - u d := by omega
  have e3 : 2 ∣ u a - u b - u c + u d := by omega
  intro r; simp only [gact]
  have ha := h a; have hb := h b; have hc := h c; have hd := h d
  split_ifs
  · rw [half_cast hev]; push_cast; rw [← ha, ← hb, ← hc, ← hd]; ring
  · rw [half_cast e1]; push_cast; rw [← ha, ← hb, ← hc, ← hd]; ring
  · rw [half_cast e2]; push_cast; rw [← ha, ← hb, ← hc, ← hd]; ring
  · rw [half_cast e3]; push_cast; rw [← ha, ← hb, ← hc, ← hd]; ring
  · exact h r

/-- `K` at one scale up. -/
theorem isCol_k_up {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v k u) {a b c d : Fin n}
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) :
    IsCol (gact (.k a b c d h₁ h₂ h₃) v) (k + 1) (fun r =>
      if r = a then u a + u b + u c + u d
      else if r = b then u a - u b + u c - u d
      else if r = c then u a + u b - u c - u d
      else if r = d then u a - u b - u c + u d
      else 2 * u r) := by
  intro r; simp only [gact]
  have ha := h a; have hb := h b; have hc := h c; have hd := h d; have hr := h r
  split_ifs <;> push_cast <;> rw [pow_succ] <;>
    first
    | (rw [← ha, ← hb, ← hc, ← hd]; ring)
    | (rw [← hr]; ring)

/-- Halving an even integer column. -/
theorem isCol_down {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (h : IsCol v (k + 1) u)
    (he : ∀ r, 2 ∣ u r) : IsCol v k (fun r => u r / 2) := by
  intro r
  rw [half_cast (he r), ← h r, pow_succ]; ring

theorem isCol_ext {v : Fin n → ℝ} {k : ℕ} {u u' : Fin n → ℤ} (h : IsCol v k u)
    (e : ∀ r, u r = u' r) : IsCol v k u' := fun r => (h r).trans (by rw [e r])

/-! ## `lde`, odd entries and the level from an integer column -/

theorem lde_eq {V : O_ZHalf n} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol (pcol V) k u) (hk : 0 < k)
    (ho : ∃ r, Odd (u r)) : lde V = k := by
  apply le_antisymm (lde_le V hc.intAt)
  by_contra hlt
  push Not at hlt
  have hi : IntAt (pcol V) (k - 1) := intAt_mono (intAt_lde V) (by omega)
  obtain ⟨r, hr⟩ := ho
  obtain ⟨z, hz⟩ := hi r
  have : (u r : ℝ) = 2 * z := by
    rw [← hc r, ← hz]
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
    ring
  have hz' : u r = 2 * z := by exact_mod_cast this
  rw [hz'] at hr
  exact Int.not_even_iff_odd.2 hr (even_two_mul z)

theorem lde_lt {V : O_ZHalf n} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol (pcol V) k u) (hk : 0 < k)
    (he : ∀ r, 2 ∣ u r) : lde V < k := by
  have : IsCol (pcol V) (k - 1) (fun r => u r / 2) := by
    apply isCol_down; rwa [Nat.sub_add_cancel hk]; exact he
  have := lde_le V this.intAt
  omega

theorem wint_eq {V : O_ZHalf n} {u : Fin n → ℤ} (hc : IsCol (pcol V) (lde V) u) (r : Fin n) :
    wint V r = u r := by
  have := (wint_spec V r).symm.trans (hc r)
  exact_mod_cast this

theorem oddSet_eq {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) :
    oddSet v k = Finset.univ.filter fun r => Odd (u r) := by
  ext r
  simp only [oddSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, ho⟩
    have : u r = z := by have := (hc r).symm.trans hz; exact_mod_cast this
    rwa [this]
  · intro ho; exact ⟨u r, hc r, ho⟩

theorem oddS_eq {V : O_ZHalf n} {u : Fin n → ℤ} (hc : IsCol (pcol V) (lde V) u) :
    oddS V = Finset.univ.filter fun r => Odd (u r) := oddSet_eq hc

theorem nodd_eq {V : O_ZHalf n} {u : Fin n → ℤ} (hc : IsCol (pcol V) (lde V) u)
    (hk : 0 < lde V) : nodd V = (Finset.univ.filter fun r => Odd (u r)).card := by
  unfold nodd; rw [if_neg (by omega)]; exact congrArg _ (oddS_eq hc)

/-! ## The first four odd entries -/

theorem orderEmbOfFin_eq_of_count {s : Finset (Fin n)} {k : ℕ} (h : s.card = k) (i : Fin k)
    {x : Fin n} (hx : x ∈ s) (hc : (s.filter (· < x)).card = i) : s.orderEmbOfFin h i = x := by
  set y := s.orderEmbOfFin h i
  have hy : y ∈ s := Finset.orderEmbOfFin_mem s h i
  have hcy : (s.filter (· < y)).card = i := by
    have : s.filter (· < y) = (Finset.Iio i).map (s.orderEmbOfFin h).toEmbedding := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
        RelEmbedding.coe_toEmbedding]
      constructor
      · rintro ⟨hz, hzy⟩
        have : z ∈ Set.range (s.orderEmbOfFin h) := by
          rw [Finset.range_orderEmbOfFin]; exact hz
        obtain ⟨j, rfl⟩ := this
        exact ⟨j, (s.orderEmbOfFin h).lt_iff_lt.1 hzy, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨Finset.orderEmbOfFin_mem s h j, (s.orderEmbOfFin h).lt_iff_lt.2 hj⟩
    rw [this, Finset.card_map, Fin.card_Iio]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (s.filter (· < y)).card < (s.filter (· < x)).card := by
      apply Finset.card_lt_card
      refine ⟨fun z hz => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hlt⟩
      · have := hsub (Finset.mem_filter.2 ⟨hy, hlt⟩)
        simp at this
    omega
  · have : (s.filter (· < x)).card < (s.filter (· < y)).card := by
      apply Finset.card_lt_card
      refine ⟨fun z hz => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hlt⟩
      · have := hsub (Finset.mem_filter.2 ⟨hx, hlt⟩)
        simp at this
    omega

/-- The first four odd entries, given four odd entries with every other one
after them. -/
theorem firstOdd_eq (U : O_ZHalf n) (h4 : 4 ≤ (oddS U).card) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS U) (hb : b ∈ oddS U) (hc : c ∈ oddS U) (hd : d ∈ oddS U)
    (hrest : ∀ r ∈ oddS U, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) :
    firstOdd U h4 0 = a ∧ firstOdd U h4 1 = b ∧ firstOdd U h4 2 = c ∧ firstOdd U h4 3 = d := by
  have hab' := Fin.lt_def.1 hab; have hbc' := Fin.lt_def.1 hbc; have hcd' := Fin.lt_def.1 hcd
  have cnt : ∀ (x : Fin n) (T : Finset (Fin n)), (∀ r, r ∈ (oddS U).filter (· < x) ↔ r ∈ T) →
      ((oddS U).filter (· < x)).card = T.card := fun x T hT => by
    rw [show (oddS U).filter (· < x) = T from Finset.ext hT]
  have key : ∀ r, r ∈ oddS U → (r : ℕ) = a ∨ (r : ℕ) = b ∨ (r : ℕ) = c ∨ (r : ℕ) = d ∨
      (d : ℕ) < r := fun r hr => by
    rcases hrest r hr with h | h | h | h | h
    · left; rw [h]
    · right; left; rw [h]
    · right; right; left; rw [h]
    · right; right; right; left; rw [h]
    · right; right; right; right; exact Fin.lt_def.1 h
  refine ⟨orderEmbOfFin_eq_of_count rfl _ ha ?_, orderEmbOfFin_eq_of_count rfl _ hb ?_,
    orderEmbOfFin_eq_of_count rfl _ hc ?_, orderEmbOfFin_eq_of_count rfl _ hd ?_⟩
  · rw [cnt a ∅ (fun r => by
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hr hlt; have := Fin.lt_def.1 hlt; rcases key r hr with h | h | h | h | h <;> omega)]
    rfl
  · rw [cnt b {a} (fun r => by
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hlt⟩; have := Fin.lt_def.1 hlt
        apply Fin.ext; rcases key r hr with h | h | h | h | h <;> omega
      · rintro rfl; exact ⟨ha, hab⟩)]
    rfl
  · rw [cnt c {a, b} (fun r => by
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hlt⟩; have := Fin.lt_def.1 hlt
        rcases key r hr with h | h | h | h | h
        · left; exact Fin.ext h
        · right; exact Fin.ext h
        all_goals omega
      · rintro (rfl | rfl)
        · exact ⟨ha, hab.trans hbc⟩
        · exact ⟨hb, hbc⟩)]
    rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hab])]; rfl
  · rw [cnt d {a, b, c} (fun r => by
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hlt⟩; have := Fin.lt_def.1 hlt
        rcases key r hr with h | h | h | h | h
        · left; exact Fin.ext h
        · right; left; exact Fin.ext h
        · right; right; exact Fin.ext h
        all_goals omega
      · rintro (rfl | rfl | rfl)
        · exact ⟨ha, hab.trans (hbc.trans hcd)⟩
        · exact ⟨hb, hbc.trans hcd⟩
        · exact ⟨hc, hcd⟩)]
    rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hab, ne_of_lt (hab.trans hbc)]),
      Finset.card_insert_of_notMem (by simp [ne_of_lt hbc])]; rfl

/-- The syllable at `k > 0`, given its four odd entries. -/
theorem syll_eq_pos (U : O_ZHalf n) (hU : 0 < pivotJ U) (hk : 0 < lde U) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS U) (hb : b ∈ oddS U) (hc : c ∈ oddS U) (hd : d ∈ oddS U)
    (hrest : ∀ r ∈ oddS U, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) :
    syll U = Gen.k a b c d hab hbc hcd :: signs U [a, b, c, d] := by
  rw [syll_pos U hU hk]
  obtain ⟨e0, e1, e2, e3⟩ := firstOdd_eq U (card_oddS U hU hk) hab hbc hcd ha hb hc hd hrest
  simp only [e0, e1, e2, e3]

end QCert.LiRossSelinger
