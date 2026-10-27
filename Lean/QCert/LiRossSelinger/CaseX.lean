/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, the edges `X_[x,x+1]` at `k > 0` that rename the syllable

Case 1.2 of the proof of Lemma A.20 when the transposition of `x` and
`x + 1` does not exchange one of the first four odd entries `a, b, c, d`
with another odd entry: Subcases 1.2.1, 1.2.2.1, 1.2.2.2 and the even half
of 1.2.2.3.  Then the syllable of `G s` is that of `s` with `x` and `x + 1`
exchanged, and the square is closed by `G` itself (`squareX_rename`).
-/
import QCert.LiRossSelinger.SwapConj

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-! ## Common facts about the edges of the Main Lemma -/

/-- An edge that does not raise the level lies below the pivot. -/
theorem extent_lt_of_le {s : O_ZHalf n} (hs : s ≠ 1) {g : Gen n}
    (hle : level (sem n g * s) ≤ level s) : extent g < pivotJ s := by
  by_contra hge
  push Not at hge
  have h1 := extent_lt_pivot s g
  have hp : pivotJ s < pivotJ (sem n g * s) := by
    rcases le_total (pivotJ s) (pivotJ (sem n g * s)) with h | h
    · rw [max_eq_right h] at h1; omega
    · rw [max_eq_left h] at h1; omega
  have hs0 : 0 < pivotJ s := Nat.pos_of_ne_zero (fun h => hs ((pivotJ_eq_zero_iff s).1 h))
  have : level s < level (sem n g * s) := by
    rw [level_eq_mk s hs0]
    refine lt_of_lt_of_le ?_ (mkLevel_le_level _)
    rw [mkLevel_lt_iff]; left; exact hp
  exact absurd hle (not_le.2 this)

theorem pivot_pos {s : O_ZHalf n} (hs : s ≠ 1) : 0 < pivotJ s :=
  Nat.pos_of_ne_zero (fun h => hs ((pivotJ_eq_zero_iff s).1 h))

/-- A column with an odd entry at a positive scale is not a unit column. -/
theorem not_unit_of_odd {v : Fin n → ℝ} {k : ℕ} {u : Fin n → ℤ} (hc : IsCol v k u) (hk : 0 < k)
    {r : Fin n} (ho : Odd (u r)) (p : Fin n) : ¬ IsUnitAt v p := by
  intro hu
  have h := hc r
  rw [hu r] at h
  have hev : Even (u r) := by
    split_ifs at h
    · have : (u r : ℝ) = ((2 ^ k : ℤ) : ℝ) := by push_cast; linarith
      rw [Int.cast_injective this]; exact Int.even_pow.2 ⟨even_two, by omega⟩
    · have : (u r : ℝ) = ((0 : ℤ) : ℝ) := by push_cast; linarith
      rw [Int.cast_injective this]; exact ⟨0, rfl⟩
  exact Int.not_even_iff_odd.2 ho hev

theorem lift_single (g : Gen n) :
    FreeMonoid.lift (sem n) (FreeMonoid.ofList [g]) = sem n g := by
  simp [FreeMonoid.lift_eval_of]

theorem wact_single (g : Gen n) (v : Fin n → ℝ) : wact [g] v = gact g v := rfl

/-- The state `G s` for a generator below the pivot whose column keeps an odd
entry at the scale of `s`. -/
theorem state_gen {s : O_ZHalf n} (hs : s ≠ 1) {g : Gen n} (hb : extent g < pivotJ s)
    {k : ℕ} {u : Fin n → ℤ} (hc : IsCol (gact g (pcol s)) k u) (hk : 0 < k) {r : Fin n}
    (ho : Odd (u r)) :
    pivotJ (sem n g * s) = pivotJ s ∧ pcol (sem n g * s) = gact g (pcol s) ∧
      lde (sem n g * s) = k := by
  have hU := pivot_pos hs
  have hl : BelowJ (pivotJ s) [g] := by
    intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']; exact hb
  obtain ⟨h1, h2⟩ := pcol_word s hU [g] hl
    (not_unit_of_odd (by rw [wact_single]; exact hc) hk ho _)
  rw [lift_single] at h1 h2
  rw [wact_single] at h2
  refine ⟨h1, h2, lde_eq (by rw [h2]; exact hc) hk ⟨r, ho⟩⟩

/-- Generators commuting with `w` commute with a word of them. -/
theorem comm_list {w : Word (Gen n)} :
    ∀ {l : List (Gen n)}, (∀ h ∈ l, Derivable (Table1 n) (FreeMonoid.of h * w) (w * FreeMonoid.of h)) →
      Derivable (Table1 n) (FreeMonoid.ofList l * w) (w * FreeMonoid.ofList l)
  | [], _ => by simp only [FreeMonoid.ofList_nil, one_mul, mul_one]; exact Derivable.refl _
  | h :: l, hc => by
    have ih := comm_list (l := l) (fun h' hh' => hc h' (List.mem_cons_of_mem _ hh'))
    rw [FreeMonoid.ofList_cons]
    have e1 := (Derivable.refl (FreeMonoid.of h)).mul ih
    have e2 := (hc h (List.mem_cons_self)).mul (Derivable.refl (FreeMonoid.ofList l))
    exact (deq (by simp only [mul_assoc])).trans (e1.trans
      ((deq (by simp only [mul_assoc])).trans (e2.trans (deq (by simp only [mul_assoc])))))

theorem rest_of_firstOdd (U : O_ZHalf n) (h4 : 4 ≤ (oddS U).card) :
    ∀ r ∈ oddS U, r = firstOdd U h4 0 ∨ r = firstOdd U h4 1 ∨ r = firstOdd U h4 2 ∨
      r = firstOdd U h4 3 ∨ firstOdd U h4 3 < r := by
  intro r hr
  have : r ∈ Set.range ((oddS U).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hr
  obtain ⟨i, rfl⟩ := this
  have hi := i.2
  by_cases h0 : i.val = 0
  · left; unfold firstOdd; congr 1; exact Fin.ext h0
  by_cases h1 : i.val = 1
  · right; left; unfold firstOdd; congr 1; exact Fin.ext h1
  by_cases h2 : i.val = 2
  · right; right; left; unfold firstOdd; congr 1; exact Fin.ext h2
  by_cases h3 : i.val = 3
  · right; right; right; left; unfold firstOdd; congr 1; exact Fin.ext h3
  right; right; right; right
  unfold firstOdd
  exact ((oddS U).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 (by simp; omega))

/-! ## The renaming squares -/

theorem mem_oddS_iff {U : O_ZHalf n} (r : Fin n) : r ∈ oddS U ↔ Odd (wint U r) := by
  rw [oddS_eq (isCol_pcol U)]; simp

theorem signs_map (U V : O_ZHalf n) (σ : Fin n → Fin n) (l : List (Fin n))
    (hw : ∀ r ∈ l, wint V (σ r) = wint U r) :
    signs V (l.map σ) = ((l.filter fun r => tau (wint U r)).map σ).map Gen.neg := by
  unfold signs
  rw [List.filter_map]
  congr 2
  apply List.filter_congr
  intro r hr
  simp [hw r hr]

/-- Subcases 1.2.1, 1.2.2.1, 1.2.2.2, 1.2.2.3 (`u_e` even). -/
theorem squareX_rename {s : O_ZHalf n} (hs : s ≠ 1) {x y : Fin n} (hxy : x < y)
    (hy : y.val = x.val + 1) (hle : level (sem n (Gen.x x y hxy) * s) ≤ level s)
    (hk : 0 < lde s) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r)
    (h1 : ¬ (x ∈ [a, b, c, d] ∧ y ∈ [a, b, c, d])) (h2 : ¬ (d = x ∧ y ∈ oddS s)) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.x x y hxy) * s)) *
        FreeMonoid.of (Gen.x x y hxy)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  set σ := Equiv.swap x y with hσ
  set V := sem n (Gen.x x y hxy) * s
  have hcV : IsCol (gact (Gen.x x y hxy) (pcol s)) (lde s) (fun r => wint s (σ r)) :=
    isCol_x (isCol_pcol s) hxy
  have hoa : Odd (wint s a) := (mem_oddS_iff a).1 ha
  have hσσ : ∀ r, σ (σ r) = r := Equiv.swap_apply_self x y
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (extent_lt_of_le hs hle) hcV hk
    (r := σ a) (by simp only [hσσ]; exact hoa)
  have hcV' : IsCol (pcol V) (lde V) (fun r => wint s (σ r)) := by rw [hcolV, hkV]; exact hcV
  have hmemV : ∀ r, r ∈ oddS V ↔ σ r ∈ oddS s := by
    intro r; rw [oddS_eq hcV', mem_oddS_iff]; simp
  have hwV : ∀ r, wint V (σ r) = wint s r := fun r => by rw [wint_eq hcV' (σ r), hσσ]
  -- the order of the renamed entries
  have hmem : ∀ z, z ∈ [a, b, c, d] ↔ z = a ∨ z = b ∨ z = c ∨ z = d := by simp
  have o1 : σ a < σ b := swap_lt hy hab (fun ⟨e1, e2⟩ => h1 ⟨by simp [e1.symm], by simp [e2.symm]⟩)
  have o2 : σ b < σ c := swap_lt hy hbc (fun ⟨e1, e2⟩ => h1 ⟨by simp [e1.symm], by simp [e2.symm]⟩)
  have o3 : σ c < σ d := swap_lt hy hcd (fun ⟨e1, e2⟩ => h1 ⟨by simp [e1.symm], by simp [e2.symm]⟩)
  have hkV0 : 0 < lde V := by rw [hkV]; exact hk
  have hsyllV : syll V = Gen.k (σ a) (σ b) (σ c) (σ d) o1 o2 o3 :: signs V [σ a, σ b, σ c, σ d] := by
    apply syll_eq_pos V (by rw [hpV]; exact hU) hkV0 o1 o2 o3
    · rw [hmemV, hσσ]; exact ha
    · rw [hmemV, hσσ]; exact hb
    · rw [hmemV, hσσ]; exact hc
    · rw [hmemV, hσσ]; exact hd
    · intro r hr
      rw [hmemV] at hr
      rcases hrest _ hr with e | e | e | e | e
      · left; rw [← e, hσσ]
      · right; left; rw [← e, hσσ]
      · right; right; left; rw [← e, hσσ]
      · right; right; right; left; rw [← e, hσσ]
      · right; right; right; right
        have := swap_lt hy e (fun ⟨e1, e2⟩ => h2 ⟨e1, by rw [← e2]; exact hr⟩)
        rwa [hσσ] at this
  have hsylls : syll s = Gen.k a b c d hab hbc hcd :: signs s [a, b, c, d] :=
    syll_eq_pos s hU hk hab hbc hcd ha hb hc hd hrest
  have hsig : signs V [σ a, σ b, σ c, σ d] =
      (([a, b, c, d].filter fun r => tau (wint s r)).map σ).map Gen.neg :=
    signs_map s V σ [a, b, c, d] (fun r _ => hwV r)
  have hF : List.Forall₂ (SwapOf x y) (syll s) (syll V) := by
    rw [hsyllV, hsylls, hsig]
    refine .cons ⟨rfl, rfl, h1⟩ ?_
    exact swapOf_negs hxy _
  refine square_short hs hle [Gen.x x y hxy] (by simp) ?_
  rw [FreeMonoid.ofList_singleton]
  exact conj_swap_list hxy hy hF

end QCert.LiRossSelinger
