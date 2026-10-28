/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Squares closed by a path with at most one `K`

A path `P = X g Y` from `next s` whose letters other than `g` are `(−1)` and
`X` generators below the pivot of `s` stays below `level s` as soon as its
end `q` does: the states along `Y` are signed permutations of `next s`, and
the states along `X` are signed permutations of `q` (every generator is an
involution).  So such a square needs only the derivation (`square_sp`).
This is the level argument of Subcases 3.2.3 and 3.2.5 of the paper.
-/
import QCert.LiRossSelinger.CaseK
import QCert.LiRossSelinger.Derive

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

theorem fixCols_mono {M : Matrix (Fin n) (Fin n) ℝ} {J J' : ℕ} (h : FixCols M J) (hJ : J ≤ J') :
    FixCols M J' :=
  fun i hi r => h i (le_trans hJ hi) r

theorem fixCols_next (U : O_ZHalf n) : FixCols (mat (next U)) (pivotJ U) := by
  by_cases hU : U = 1
  · subst hU
    rw [next_one]
    intro i _ r
    show (1 : Matrix (Fin n) (Fin n) ℝ) r i = _
    rw [Matrix.one_apply]
  have h := pivot_pos hU
  rcases Nat.eq_zero_or_pos (lde U) with hk | hk
  · exact fixCols_mono (next_zero U h hk) (by omega)
  · exact (next_pos U h hk).1

theorem fixCols_iterN (m : ℕ) : ∀ (U : O_ZHalf n) {J : ℕ}, FixCols (mat U) J →
    FixCols (mat (iterN m U)) J := by
  induction m with
  | zero => intro U J h; exact h
  | succ m ih =>
    intro U J h
    exact ih (next U) (fixCols_mono (fixCols_next U) (pivotJ_le_of U h))

theorem lift_rev_mul (l : List (Gen n)) :
    FreeMonoid.lift (sem n) (FreeMonoid.ofList l.reverse) *
      FreeMonoid.lift (sem n) (FreeMonoid.ofList l) = 1 := by
  have := derivable_sound sound (self_inv' l)
  simpa [FreeMonoid.ofList_append, map_mul] using this

/-- A `(−1)` or `X` letter below the pivot of `s`. -/
def SPBelow (s : O_ZHalf n) (g : Gen n) : Prop := g.tag ≠ 2 ∧ extent g < pivotJ s

theorem level_sp_word {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) :
    ∀ (l : List (Gen n)), (∀ g ∈ l, SPBelow s g) → ∀ {t : O_ZHalf n},
      FixCols (mat t) (pivotJ s) → level t < level s →
      FixCols (mat (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * t)) (pivotJ s) ∧
        level (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * t) < level s
  | [], _, t, hF, hL => by simpa using ⟨hF, hL⟩
  | g :: l, hl, t, hF, hL => by
    obtain ⟨hF', hL'⟩ :=
      level_sp_word hs hk l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) hF hL
    have hg := hl g List.mem_cons_self
    rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of, mul_assoc]
    exact ⟨fixCols_gen hF' hg.2, level_signed_lt hs hk hF' hL' hg.1 hg.2⟩

/-- The inner states of a path `X g Y` from `next s` to `q`. -/
theorem path_sp {s q : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) (Xw Yw : List (Gen n))
    (g : Gen n) (hX : ∀ x ∈ Xw, SPBelow s x) (hY : ∀ x ∈ Yw, SPBelow s x)
    (hq : FreeMonoid.lift (sem n) (FreeMonoid.ofList (Xw ++ g :: Yw)) * next s = q)
    (hqF : FixCols (mat q) (pivotJ s)) (hqL : level q < level s) :
    ∀ i, 0 < i → i < (Xw ++ g :: Yw).length →
      level (FreeMonoid.lift (sem n) (FreeMonoid.ofList ((Xw ++ g :: Yw).drop i)) * next s) <
        level s := by
  intro i hi0 hi
  have htF : FixCols (mat (next s)) (pivotJ s) := fixCols_next s
  have htL := level_next_lt s hs
  by_cases hiX : Xw.length < i
  · obtain ⟨k, rfl⟩ : ∃ k, i = Xw.length + 1 + k := ⟨i - Xw.length - 1, by omega⟩
    have e : (Xw ++ g :: Yw).drop (Xw.length + 1 + k) = Yw.drop k := by
      rw [show Xw.length + 1 + k = Xw.length + (k + 1) by omega, List.drop_length_add_append]
      rfl
    rw [e]
    exact (level_sp_word hs hk (Yw.drop k) (fun x hx => hY x (List.mem_of_mem_drop hx))
      htF htL).2
  · push Not at hiX
    set A := Xw.take i
    set B := (Xw ++ g :: Yw).drop i
    have hAB : Xw ++ g :: Yw = A ++ B := by
      rw [← List.take_append_drop i (Xw ++ g :: Yw), List.take_append_of_le_length hiX]
    have hB : FreeMonoid.lift (sem n) (FreeMonoid.ofList B) * next s =
        FreeMonoid.lift (sem n) (FreeMonoid.ofList A.reverse) * q := by
      rw [← hq, hAB, FreeMonoid.ofList_append, map_mul, ← mul_assoc, ← mul_assoc,
        lift_rev_mul, one_mul]
    rw [hB]
    exact (level_sp_word hs hk A.reverse (fun x hx => hX x (List.mem_of_mem_take
      (List.mem_reverse.1 hx))) hqF hqL).2

/-- A square of the Main Lemma closed by a path `X g Y` whose letters other
than `g` are `(−1)` and `X` generators below the pivot. -/
theorem square_sp {s : O_ZHalf n} {G : Gen n} (hs : s ≠ 1) (hk : 0 < lde s)
    (hle : level (sem n G * s) ≤ level s) (m : ℕ) (hm : 0 < m ∨ level (sem n G * s) < level s)
    (Xw Yw : List (Gen n)) (g : Gen n) (hX : ∀ x ∈ Xw, SPBelow s x) (hY : ∀ x ∈ Yw, SPBelow s x)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n G * s)) * FreeMonoid.of G)
      (FreeMonoid.ofList (Xw ++ g :: Yw) * FreeMonoid.ofList (syll s))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n G * s)) * FreeMonoid.of G)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hsem := derivable_sound sound hder
  simp only [map_mul, FreeMonoid.lift_eval_of] at hsem
  have hq : FreeMonoid.lift (sem n) (FreeMonoid.ofList (Xw ++ g :: Yw)) * next s =
      iterN m (sem n G * s) := by
    rw [iterN_eq, next, ← mul_assoc, ← hsem, mul_assoc]
  have hqF : FixCols (mat (iterN m (sem n G * s))) (pivotJ s) :=
    fixCols_iterN m _ (fixCols_gen (fixCols_pivotJ s) (extent_lt_of_le hs hle))
  have hqL : level (iterN m (sem n G * s)) < level s := by
    rcases hm with hm | hlt
    · exact level_iterN_lt hm _ hs hle
    · exact lt_of_le_of_lt (level_iterN_le m _) hlt
  exact square hs hle m (Xw ++ g :: Yw) hm hder
    (path_sp hs hk Xw Yw g hX hY hq hqF hqL)

/-- A square closed by a path of `(−1)` and `X` letters below the pivot. -/
theorem square_sp0 {s : O_ZHalf n} {G : Gen n} (hs : s ≠ 1) (hk : 0 < lde s)
    (hle : level (sem n G * s) ≤ level s) (m : ℕ) (hm : 0 < m ∨ level (sem n G * s) < level s)
    (Yw : List (Gen n)) (hY : ∀ x ∈ Yw, SPBelow s x)
    (hder : Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n G * s)) * FreeMonoid.of G)
      (FreeMonoid.ofList Yw * FreeMonoid.ofList (syll s))) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n G * s)) * FreeMonoid.of G)
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) :=
  square hs hle m Yw hm hder (fun i _ _ =>
    (level_sp_word hs hk (Yw.drop i) (fun x hx => hY x (List.mem_of_mem_drop hx))
      (fixCols_next s) (level_next_lt s hs)).2)

/-- A word below the pivot whose integer column at the scale of `s` has
strictly fewer odd entries lowers the level. -/
theorem level_lt_of_col {s : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s) (l : List (Gen n))
    (hl : BelowJ (pivotJ s) l) {u' : Fin n → ℤ} (hc : IsCol (wact l (pcol s)) (lde s) u')
    (hsub : ∀ r, Odd (u' r) → Odd (wint s r)) {r₀ : Fin n} (hr₀ : Odd (wint s r₀))
    (hr₀' : ¬ Odd (u' r₀)) :
    level (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * s) < level s := by
  have hU := pivot_pos hs
  by_cases hu : IsUnitAt (wact l (pcol s)) (pidx s hU)
  · exact level_lt_of hU (Or.inl (pivot_word_lt s hU l hl hu))
  obtain ⟨hp, hcol⟩ := pcol_word s hU l hl hu
  set V := FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * s
  have hc' : IsCol (pcol V) (lde s) u' := by rw [hcol]; exact hc
  apply level_lt_of hU
  right
  refine ⟨hp, ?_⟩
  by_cases ho : ∃ r, Odd (u' r)
  · have hl' := lde_eq hc' hk ho
    right
    refine ⟨hl', ?_⟩
    rw [← hl'] at hc'
    rw [nodd_eq hc' (by rw [hl']; exact hk)]
    unfold nodd
    rw [if_neg (by omega), oddSet_eq (isCol_pcol s)]
    apply Finset.card_lt_card
    refine ⟨fun r hr => ?_, fun hsub' => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hsub r hr
    · have := hsub' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr₀⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hr₀' this
  · push Not at ho
    left
    exact lde_lt hc' hk (fun r => even_iff_two_dvd.1 (Int.not_odd_iff_even.1 (ho r)))

/-! ## Renamed words -/

theorem negw_rename {m : ℕ} (f : Fin m ↪o Fin n) (t : Bool) (i : Fin m) :
    (negw t i).map (Gen.rename f) = negw t (f i) := by
  cases t <;> rfl

theorem tag_rename {m : ℕ} (f : Fin m ↪o Fin n) (g : Gen m) : (g.rename f).tag = g.tag := by
  cases g <;> rfl

theorem extent_rename_le {m : ℕ} (f : Fin m ↪o Fin n) (g : Gen m) (k : Fin m)
    (hk : extent g ≤ k.val) : extent (g.rename f) ≤ (f k).val := by
  cases g with
  | neg a => exact Fin.le_def.1 (f.monotone (Fin.le_def.2 hk))
  | x a b h => exact Fin.le_def.1 (f.monotone (Fin.le_def.2 hk))
  | k a b c d h₁ h₂ h₃ => exact Fin.le_def.1 (f.monotone (Fin.le_def.2 hk))

theorem extent_le_last {m : ℕ} (g : Gen (m + 1)) : extent g ≤ (Fin.last m).val := by
  cases g with
  | neg a => exact Nat.lt_succ_iff.1 a.2
  | x a b h => exact Nat.lt_succ_iff.1 b.2
  | k a b c d h₁ h₂ h₃ => exact Nat.lt_succ_iff.1 d.2

theorem signs4 (U : O_ZHalf n) (x0 x1 x2 x3 : Fin n) :
    signs U [x0, x1, x2, x3] = negw (tau (wint U x0)) x0 ++ negw (tau (wint U x1)) x1 ++
      negw (tau (wint U x2)) x2 ++ negw (tau (wint U x3)) x3 := by
  simp only [signs_cons, negw, List.append_assoc]
  simp [signs]

end QCert.LiRossSelinger
