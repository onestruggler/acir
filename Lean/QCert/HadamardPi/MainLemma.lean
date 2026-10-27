/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.7, the Main Lemma

For a basic generator `G` (`X_[0,x]`, `(-1)_[0]`, `H_[0,1]`) at a state
`s ≠ I` with first syllable `N : s ⇒ t`, the square closes strictly below
`s` (`MainSquare`).  The paper splits the proof into twelve cases by `G` and
the shape of `N` (Table 2 of the appendix; Main Cases 1–12).

Three patterns close most squares:
* `square_pro`: the syllable of `s` is `G` itself;
* `square_retro`: the syllable of `G s` is `G` (in particular when `G` acts
  at or above the pivot);
* `square_of`: the syllable `N'` of `G s` and a path `G'` from `t` with
  `N' G ≈ G' N`, below `s`.
-/
import QCert.HadamardPi.Paths
import QCert.HadamardPi.Rel

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### Closing patterns -/

section Patterns

variable {s : O n}

/-- The syllable of `s` is `G`: take `N' = G' = ε`. -/
theorem square_pro (hs : s ≠ 1) {g : Gen n} (h : syl s = FreeMonoid.of g) : MainSquare s g := by
  refine ⟨sem n g * s, [], [], by simp, ?_, ?_, ?_⟩
  · rw [run_nil, h, FreeMonoid.lift_eval_of]
  · exact lev_syl_lt hs
  · rw [h]

/-- The syllable of `G s` is `G`: from `G s` the normal path goes back to
`s` and then follows `N`. -/
theorem square_retro (hs : s ≠ 1) {g : Gen n} (h : syl (sem n g * s) = FreeMonoid.of g) :
    MainSquare s g := by
  have hr : sem n g * s ≠ 1 := by
    intro h1
    rw [h1, syl, dif_neg (by rw [piv_eq_zero_iff.2 rfl]; omega)] at h
    exact absurd (congrArg FreeMonoid.toList h) (by simp)
  refine ⟨FreeMonoid.lift (sem n) (syl s) * s, (syl s * FreeMonoid.of g).toList, [], ?_, ?_, ?_, ?_⟩
  · rw [nw_of_ne hr, h, FreeMonoid.lift_eval_of, sem_sq_assoc, nw_of_ne hs, ofList_toList,
      mul_assoc]
  · rw [run_nil]
  · exact lev_syl_lt hs
  · rw [ofList_toList, mul_assoc]
    have hg : Derivable Fig6 (FreeMonoid.of g * FreeMonoid.of g) 1 := by
      cases g with
      | Z a => exact Derivable.of (Fig6.a1 a)
      | X a b hab => exact Derivable.of (Fig6.a2 hab)
      | H a b hab => exact Derivable.of (Fig6.a3 hab)
    simpa using (Derivable.refl (syl s)).mul hg

/-- The general square: the syllable `N'` of `G s`, and a path `G'` from
`t` below `s` with `N' G ≈ G' N`. -/
theorem square_of (hs : s ≠ 1) {g : Gen n} (hr : sem n g * s ≠ 1) (G' : List (Gen n))
    (hpath : PathLt (lev s) G' (FreeMonoid.lift (sem n) (syl s) * s))
    (hder : Derivable Fig6 (syl (sem n g * s) * FreeMonoid.of g) (ofList G' * syl s)) :
    MainSquare s g := by
  have hsound := derivable_sound fig6_sound hder
  simp only [map_mul, FreeMonoid.lift_eval_of] at hsound
  refine ⟨FreeMonoid.lift (sem n) (syl (sem n g * s)) * (sem n g * s),
    (syl (sem n g * s)).toList, G', ?_, ?_, hpath, ?_⟩
  · rw [nw_of_ne hr, ofList_toList]
  · rw [run, ← mul_assoc, ← hsound, mul_assoc]
  · rwa [ofList_toList]

end Patterns

/-! ### Pivots -/

section Pivots

variable {s : O n}

theorem piv_pos (hs : s ≠ 1) : 0 < piv s := Nat.pos_of_ne_zero fun h => hs (piv_eq_zero_iff.1 h)

theorem pj_val (hp : 0 < piv s) : ((pj s hp : Fin n) : ℕ) = piv s - 1 := rfl

/-- The nonzero entries of the pivot column lie below the pivot. -/
theorem pcol_low (hp : 0 < piv s) {i : Fin n} (hi : col s (pj s hp) i ≠ 0) : (i : ℕ) < piv s := by
  by_contra h
  exact hi (col_eq_zero_of_piv_le (by rw [pj_val]; omega) (by omega))

/-- A generator below `B` keeps the pivot below `B`. -/
theorem piv_le_of_idx {u : O n} {g : Gen n} {B : ℕ} (hu : piv u ≤ B)
    (hg : ∀ i ∈ g.idx, (i : ℕ) < B) : piv (sem n g * u) ≤ B := by
  apply piv_le
  intro j hj
  show col _ j = _
  rw [col_sem_mul, fixed_of_piv_le (hu.trans hj)]
  exact gv_single fun hj' => by have := hg j hj'; omega

theorem lev_lt_of_piv_lt {u : O n} (h : piv u < piv s) : lev u < lev s := lev_lt_iff.2 (Or.inl h)

/-- A generator acting below the pivot that does not fix the pivot column
keeps the pivot. -/
theorem piv_eq_of_col {g : Gen n} (hp : 0 < piv s) (hb : ∀ i ∈ g.idx, (i : ℕ) < piv s)
    (hnf : gv g (col s (pj s hp)) ≠ Pi.single (pj s hp) 1) : piv (sem n g * s) = piv s := by
  apply le_antisymm (piv_le_of_idx le_rfl hb)
  by_contra hlt
  push Not at hlt
  apply hnf
  rw [← col_sem_mul]
  exact fixed_of_piv_le (by rw [pj_val]; omega)

/-- If the pivot stays, the syllable of `G s` is read off `G` applied to
the pivot column. -/
theorem syl_of_piv_eq {g : Gen n} (hp : 0 < piv s) (h : piv (sem n g * s) = piv s) :
    syl (sem n g * s) = sylOf (pj s hp) (gv g (col s (pj s hp))) := by
  have hp' : 0 < piv (sem n g * s) := h ▸ hp
  rw [syl, dif_pos hp']
  have : pj _ hp' = pj s hp := Fin.ext (by simp only [pj]; rw [h])
  rw [this, col_sem_mul]

theorem syl_eq_sylOf (hp : 0 < piv s) : syl s = sylOf (pj s hp) (col s (pj s hp)) := by
  rw [syl, dif_pos hp]

/-- A unit vector with entry `1` at `j` is `e_j`. -/
theorem eq_single_of_one {v : Fin n → ℝ} (hU : IsUnitVec v) {j : Fin n} (h : v j = 1) :
    v = Pi.single j 1 := by
  have hs : v j * v j + ∑ i ∈ univ.erase j, v i * v i = 1 := by
    rw [Finset.add_sum_erase univ (fun i => v i * v i) (mem_univ j)]; exact hU
  rw [h, mul_one] at hs
  have hz : ∀ i ∈ univ.erase j, v i * v i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).1 (by linarith)
  funext i
  by_cases hij : i = j
  · subst hij; simp [h]
  · rw [Pi.single_eq_of_ne hij]
    exact mul_self_eq_zero.1 (hz i (mem_erase.2 ⟨hij, mem_univ i⟩))

/-- At exponent 0 the pivot column is `±e_a` with `a` at most the pivot
index, and `-e_j` if `a` is the pivot index. -/
theorem pcol_single (hp : 0 < piv s) (hk : lde (col s (pj s hp)) = 0) :
    ∃ a : Fin n, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ col s (pj s hp) = Pi.single a ε ∧
      a ≤ pj s hp ∧ (a = pj s hp → ε = -1) := by
  obtain ⟨a, ε, hε, hva⟩ := eq_single_of_lde_zero (col_inRing s _) (col_unit s _) hk
  refine ⟨a, ε, hε, hva, ?_, ?_⟩
  · have := pcol_low hp (i := a) (by rw [hva]; rcases hε with rfl | rfl <;> simp)
    rw [Fin.le_def, pj_val]; omega
  · rintro rfl
    rcases hε with rfl | rfl
    · exact absurd hva (not_fixed_pj hp)
    · rfl

/-- At exponent 0 the syllable fixes the pivot column, so the pivot drops. -/
theorem piv_t_lt (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) = 0) :
    piv (FreeMonoid.lift (sem n) (syl s) * s) < piv s := by
  have h := lev_syl_lt hs
  rcases lev_lt_iff.1 h with h | ⟨h, hkl⟩
  · exact h
  · exfalso
    have h0 : kl (pcol s) = toLex (0, 0) := by simp [kl, pcol_eq (piv_pos hs), hk]
    rw [h0] at hkl
    rcases Prod.Lex.toLex_lt_toLex.1 hkl with h1 | ⟨_, h1⟩
    · exact absurd h1 (Nat.not_lt_zero _)
    · exact absurd h1 (Nat.not_lt_zero _)

/-- `(q+1, 0, 0)` is strictly below a state at a positive exponent with
`q` below its pivot. -/
theorem lev0_lt_of_lde {q : ℕ} (hp : 0 < piv s) (hq : q < piv s)
    (hk : lde (col s (pj s hp)) ≠ 0) : lev0 q < lev s := by
  rw [lev0, lev, pcol_eq hp]
  rcases Nat.lt_or_ge (q + 1) (piv s) with h | h
  · exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
  · refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨by omega, ?_⟩)
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (Nat.pos_of_ne_zero hk))

end Pivots

/-! ### Signed basis columns -/

section Single

theorem xv_single (p q a : Fin n) (ε : ℝ) :
    xv p q (Pi.single a ε) = Pi.single (Equiv.swap p q a) ε := by
  rw [xv_eq_signed]
  funext i
  simp only [one_mul, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem lde_single {b : Fin n} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : lde (Pi.single b ε) = 0 := by
  apply lde_eq_zero_of_int
  intro i
  by_cases h : i = b
  · subst h; rcases hε with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  · exact ⟨0, by simp [h]⟩

/-- If a generator acting below the pivot sends the pivot column to a
signed basis vector other than `e_j`, the syllable of `G s` is the
signed transposition back to `e_j`. -/
theorem syl_r_single {s : O n} (hp : 0 < piv s) {g : Gen n}
    (hb : ∀ i ∈ g.idx, (i : ℕ) < piv s) {b : Fin n} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hcol : gv g (col s (pj s hp)) = Pi.single b ε) (hne : ¬(b = pj s hp ∧ ε = 1)) :
    syl (sem n g * s) = (if hlt : b < pj s hp then FreeMonoid.of (Gen.X b (pj s hp) hlt) else 1) *
      (if ε < 0 then FreeMonoid.of (Gen.Z b) else 1) := by
  have hpiv : piv (sem n g * s) = piv s := by
    apply piv_eq_of_col hp hb
    rw [hcol]
    intro h
    apply hne
    have hb' : b = pj s hp := by
      by_contra hbj
      have := congrFun h b
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hbj] at this
      rcases hε with rfl | rfl <;> norm_num at this
    refine ⟨hb', ?_⟩
    have := congrFun h (pj s hp)
    rw [← hb', Pi.single_eq_same, Pi.single_eq_same] at this
    exact this
  rw [syl_of_piv_eq hp hpiv, hcol, sylOf_zero (lde_single hε) hε rfl]

/-- At exponent 0, the syllable of `s`. -/
theorem syl_s_single {s : O n} (hp : 0 < piv s) {a : Fin n} {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hva : col s (pj s hp) = Pi.single a ε) :
    syl s = (if hlt : a < pj s hp then FreeMonoid.of (Gen.X a (pj s hp) hlt) else 1) *
      (if ε < 0 then FreeMonoid.of (Gen.Z a) else 1) := by
  rw [syl_eq_sylOf hp, hva, sylOf_zero (lde_single hε) hε rfl]

end Single

/-! ### The basic generators at or above the pivot -/

section Above

/-- `X_[0,q]` at or above the pivot: its syllable is itself. -/
theorem syl_X_above {t : O n} {z q : Fin n} (hzq : z < q) (hz : (z : ℕ) = 0) (hq : piv t ≤ q) :
    syl (sem n (Gen.X z q hzq) * t) = FreeMonoid.of (Gen.X z q hzq) := by
  have hp : piv (sem n (Gen.X z q hzq) * t) = q + 1 := piv_of_lev (lev_X_of_le hzq hq)
  have hp0 : 0 < piv (sem n (Gen.X z q hzq) * t) := by omega
  have hpj : pj _ hp0 = q := Fin.ext (by simp only [pj]; omega)
  have hcol : col (sem n (Gen.X z q hzq) * t) q = Pi.single z 1 := by
    rw [col_sem_mul, fixed_of_lt hq]
    simp only [gv]; rw [xv_single, Equiv.swap_apply_right]
  rw [syl, dif_pos hp0, hpj, hcol, sylOf_zero (lde_single (Or.inl rfl)) (Or.inl rfl) rfl,
    dif_pos hzq, if_neg (by norm_num), mul_one]

/-- The column `e (e_p ± e_q)/√2` reached by `H_[p,q]` from `±e_p` or `±e_q`
(`e = ±1`): two odd entries of the same class at exponent 1. -/
theorem hv_pm_facts {p q : Fin n} (hpq : p < q) {a : Fin n} (ha : a = p ∨ a = q) {e : ℤ}
    (he : e = 1 ∨ e = -1) :
    InRing (hv p q (Pi.single a (e : ℝ))) ∧ lde (hv p q (Pi.single a (e : ℝ))) = 1 ∧
      oddSet (hv p q (Pi.single a (e : ℝ))) = {p, q} ∧
      SameOdd (num (hv p q (Pi.single a (e : ℝ))) p) (num (hv p q (Pi.single a (e : ℝ))) q) ∧
      ∀ i, i ≠ p → i ≠ q → num (hv p q (Pi.single a (e : ℝ))) i = 0 := by
  classical
  have hne : p ≠ q := ne_of_lt hpq
  set v := hv p q (Pi.single a (e : ℝ))
  have h2 := sqrt2_mul_invSqrt2
  -- the numerators at exponent 1
  set u : Fin n → ℤ√2 := fun i =>
    if i = p then (e : ℤ√2) else if i = q then (if a = p then (e : ℤ√2) else -(e : ℤ√2)) else 0
  have hvi : ∀ i, v i = if i = p then invSqrt2 * e else if i = q then
      (if a = p then invSqrt2 * e else -(invSqrt2 * e)) else 0 := by
    intro i
    simp only [v, hv]
    rcases ha with rfl | rfl
    · by_cases h1 : i = a
      · subst h1; simp [Pi.single_apply, hne, Ne.symm hne]
      · by_cases h3 : i = q
        · subst h3; simp [Pi.single_apply, hne, Ne.symm hne]
        · simp [Pi.single_apply, h1, h3]
    · by_cases h1 : i = p
      · subst h1; simp [Pi.single_apply, hne, Ne.symm hne]
      · by_cases h3 : i = a
        · subst h3; simp [Pi.single_apply, hne, Ne.symm hne, h1]
        · simp [Pi.single_apply, h1, h3]
  have hu : ∀ i, toReal (u i) = Real.sqrt 2 ^ 1 * v i := by
    intro i
    rw [hvi i]
    simp only [u]
    split_ifs <;> simp <;> linear_combination (e : ℝ) * h2
  have hmem : ((e : ℝ)) * invSqrt2 ∈ ZInvSqrt2 := ZInvSqrt2.mul_mem (by
    rcases he with rfl | rfl
    · simpa using ZInvSqrt2.one_mem
    · simpa using ZInvSqrt2.neg_mem ZInvSqrt2.one_mem) invSqrt2_mem
  have hR : InRing v := fun i => by
    rw [hvi i]
    split_ifs
    · rw [mul_comm]; exact hmem
    · rw [mul_comm]; exact hmem
    · rw [mul_comm]; exact ZInvSqrt2.neg_mem hmem
    · exact ZInvSqrt2.zero_mem
  have hl : lde v = 1 := by
    apply le_antisymm (lde_le fun i => ⟨u i, hu i⟩)
    by_contra h0
    have h00 : lde v = 0 := by omega
    have := denV_lde hR p
    rw [h00, hvi p, if_pos rfl] at this
    rcases he with rfl | rfl
    · simp only [Int.cast_one, mul_one] at this; exact not_den_zero_invSqrt2 this
    · simp only [Int.cast_neg, Int.cast_one, mul_neg_one] at this
      exact not_den_zero_invSqrt2 (by simpa using this.neg)
  have hnum : num v = u := num_eq hR (by rw [hl]; exact hu)
  have hoddE : Odd e := by rcases he with rfl | rfl <;> decide
  refine ⟨hR, hl, ?_, ?_, ?_⟩
  · ext i
    rw [mem_oddSet, hnum]
    simp only [u, mem_insert, mem_singleton]
    split_ifs <;> simp_all [hoddE]
  · rw [hnum]
    simp only [SameOdd, u, if_pos rfl, if_neg (Ne.symm hne)]
    split_ifs <;> simp [hoddE]
  · intro i h1 h3
    rw [hnum]; simp [u, h1, h3]

/-- If the pivot column of `H_[0,1] s` is `ε (e_0 ± e_1)/√2`, its syllable
is `H_[0,1]`. -/
theorem sylOf_hv_pm {j z o a : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ha : a = z ∨ a = o) {e : ℤ} (he : e = 1 ∨ e = -1) :
    sylOf j (hv z o (Pi.single a (e : ℝ))) = FreeMonoid.of (Gen.H z o hzo) := by
  classical
  obtain ⟨hR, hl, hodd, hsame, hzero⟩ := hv_pm_facts hzo ha he
  set v := hv z o (Pi.single a (e : ℝ))
  have hk : lde v ≠ 0 := by rw [hl]; norm_num
  have h1 : (oddSet v).Nonempty := ⟨z, by rw [hodd]; simp⟩
  have hm1 : (oddSet v).min' h1 = z := by
    apply le_antisymm ((oddSet v).min'_le z (by rw [hodd]; simp))
    apply (oddSet v).le_min'
    intro y hy; rw [hodd] at hy; simp at hy; rcases hy with rfl | rfl
    · exact le_rfl
    · exact le_of_lt hzo
  have hpart : partners v ((oddSet v).min' h1) = {o} := by
    rw [hm1]; ext i
    rw [mem_partners, mem_singleton]
    constructor
    · rintro ⟨hi, hs'⟩
      by_contra hio
      have := hs'.2.1
      rw [hzero i (ne_of_gt hi) hio] at this
      simp at this
    · rintro rfl; exact ⟨hzo, hsame⟩
  have h2 : (partners v ((oddSet v).min' h1)).Nonempty := by rw [hpart]; simp
  have hm2 : (partners v ((oddSet v).min' h1)).min' h2 = o := by
    have := (partners v ((oddSet v).min' h1)).min'_mem h2
    exact mem_singleton.1 ((Finset.ext_iff.1 hpart _).1 this)
  rw [sylOf_pos hk h1 h2 z (Fin.ext hz) (by rw [hm2]; exact hzo)]
  generalize hgen : (partners v ((oddSet v).min' h1)).min' h2 = m at *
  subst hm2
  rw [dif_neg (by rw [hm1]; exact lt_irrefl _), mul_one]

/-- `H_[0,1]` at or above the pivot: its syllable is itself. -/
theorem syl_H_above {t : O n} {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0) (hq : piv t ≤ o) :
    syl (sem n (Gen.H z o hzo) * t) = FreeMonoid.of (Gen.H z o hzo) := by
  have hp : piv (sem n (Gen.H z o hzo) * t) = o + 1 := piv_of_lev (lev_H_of_le hzo hq)
  have hp0 : 0 < piv (sem n (Gen.H z o hzo) * t) := by omega
  have hpj : pj _ hp0 = o := Fin.ext (by simp only [pj]; omega)
  have hcol : col (sem n (Gen.H z o hzo) * t) o = hv z o (Pi.single o ((1 : ℤ) : ℝ)) := by
    rw [col_sem_mul, fixed_of_lt hq]; simp [gv]
  rw [syl, dif_pos hp0, hpj, hcol, sylOf_hv_pm hzo hz (Or.inr rfl) (Or.inl rfl)]

/-- The syllable of a basic generator is the generator itself. -/
theorem syl_basic (g : Gen n) (hg : Basic g) : syl (sem n g) = FreeMonoid.of g := by
  have h1 : piv (1 : O n) = 0 := piv_eq_zero_iff.2 rfl
  cases g with
  | Z a =>
    simp only [Basic] at hg
    have hp : piv (sem n (Gen.Z a) * 1) = (a : ℕ) + 1 :=
      piv_of_lev (lev_Z_of_le (t := 1) (p := a) (by rw [h1]; exact Nat.zero_le _))
    rw [mul_one] at hp
    have hp0 : 0 < piv (sem n (Gen.Z a)) := by omega
    have hpj : pj _ hp0 = a := Fin.ext (by simp only [pj]; omega)
    have hcol : col (sem n (Gen.Z a)) a = Pi.single a (-1) := by
      rw [← mul_one (sem n _), col_sem_mul, col_one]
      funext i; simp only [gv, zv]
      split_ifs with h
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [syl, dif_pos hp0, hpj, hcol, sylOf_zero (lde_single (Or.inr rfl)) (Or.inr rfl) rfl,
      dif_neg (lt_irrefl _), if_pos (by norm_num), one_mul]
  | X a b hab =>
    simp only [Basic] at hg
    have := syl_X_above (t := 1) hab hg (by rw [h1]; exact Nat.zero_le _)
    rwa [mul_one] at this
  | H a b hab =>
    simp only [Basic] at hg
    have := syl_H_above (t := 1) hab hg.1 (by rw [h1]; exact Nat.zero_le _)
    rwa [mul_one] at this

end Above

/-! ### Paths of signed permutations -/

section PermPaths

/-- An `X` or `(-1)` letter whose largest index `q` has `(q+1, 0, 0)` below
`L`. -/
def XZLt (L : ℕ ×ₗ (ℕ ×ₗ ℕ)) (g : Gen n) : Prop :=
  (∃ p q : Fin n, ∃ h : p < q, g = Gen.X p q h ∧ lev0 q < L) ∨ (∃ p : Fin n, g = Gen.Z p ∧ lev0 p < L)

/-- A path of such letters from a state below `L` stays below `L`. -/
theorem xz_path {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, XZLt L g) → lev t < L → PathLt L w t
  | [], _, _, h => h
  | g :: w, t, hX, h => by
    have hw := xz_path w t (fun g' hg' => hX g' (List.mem_cons_of_mem _ hg')) h
    refine ⟨hw, ?_⟩
    rw [run_cons]
    rcases hX g List.mem_cons_self with ⟨p, q, hpq, rfl, hq⟩ | ⟨p, rfl, hq⟩
    · exact lt_of_le_of_lt (lev_X_le_max hpq) (max_lt hw.last hq)
    · exact lt_of_le_of_lt lev_Z_le_max (max_lt hw.last hq)

/-- A path whose letters act below `B` from a state with pivot at most `B`
keeps the pivot at most `B`. -/
theorem piv_path {s : O n} {B : ℕ} (hB : B < piv s) :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, ∀ i ∈ g.idx, (i : ℕ) < B) → piv t ≤ B →
      PathLt (lev s) w t
  | [], _, _, h => lev_lt_of_piv_lt (by omega)
  | g :: w, t, hg, h => by
    have hw := piv_path hB w t (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) h
    refine ⟨hw, lev_lt_of_piv_lt ?_⟩
    have : piv (run w t) ≤ B := by
      clear hw
      induction w with
      | nil => simpa using h
      | cons g' w ih =>
        rw [run_cons]
        exact piv_le_of_idx (ih (fun g'' hg'' => hg g'' (by simp at hg'' ⊢; tauto)))
          (hg g' (by simp))
    rw [run_cons]
    have := piv_le_of_idx this (hg g List.mem_cons_self)
    omega

end PermPaths

/-! ### `G = (-1)_[0]`: Main Cases 5–8 -/

section CaseZ

theorem oddSet_zv {v : Fin n → ℝ} (hR : InRing v) (p : Fin n) : oddSet (zv p v) = oddSet v := by
  ext i
  simp only [mem_oddSet, num_zv p hR]
  split_ifs <;> simp [odd_neg]

theorem partners_zv {v : Fin n → ℝ} (hR : InRing v) (p : Fin n) (i : Fin n) :
    partners (zv p v) i = partners v i := by
  ext i'
  simp only [mem_partners, SameOdd, num_zv p hR]
  split_ifs <;> simp [odd_neg]

theorem sylOf_zv {j : Fin n} {v : Fin n → ℝ} (hR : InRing v) (hk : lde v ≠ 0) (p : Fin n) :
    sylOf j (zv p v) = sylOf j v := by
  have hk' : lde (zv p v) ≠ 0 := by rwa [lde_zv p hR]
  rw [sylOf_eq_sylPos hk', sylOf_eq_sylPos hk, oddSet_zv hR]
  congr 1
  funext i
  exact partners_zv hR p i

/-- The first syllable at a positive exponent, in explicit form. -/
theorem syl_pos_form {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) :
    ∃ (i1 i2 : Fin n) (z : Fin n) (hz2 : z < i2),
      (z : ℕ) = 0 ∧ z ≤ i1 ∧ i1 < i2 ∧ (i1 : ℕ) < piv s ∧ (i2 : ℕ) < piv s ∧
      Odd (num (col s (pj s (piv_pos hs))) i1).re ∧
      SameOdd (num (col s (pj s (piv_pos hs))) i1) (num (col s (pj s (piv_pos hs))) i2) ∧
      (∀ i, Odd (num (col s (pj s (piv_pos hs))) i).re → i1 ≤ i) ∧
      (∀ i, i1 < i → SameOdd (num (col s (pj s (piv_pos hs))) i1)
        (num (col s (pj s (piv_pos hs))) i) → i2 ≤ i) ∧
      syl s = FreeMonoid.of (Gen.H z i2 hz2) *
        (if hz1 : z < i1 then FreeMonoid.of (Gen.X z i1 hz1) else 1) := by
  classical
  have hp := piv_pos hs
  set v := col s (pj s hp)
  have hR : InRing v := col_inRing s _
  have hU : IsUnitVec v := col_unit s _
  have hk1 : 1 ≤ lde v := Nat.one_le_iff_ne_zero.2 hk
  obtain ⟨i0, hi0⟩ := exists_odd_num hR hk1
  have h1 : (oddSet v).Nonempty := ⟨i0, mem_oddSet.2 hi0⟩
  set i1 := (oddSet v).min' h1 with hi1
  have hi1odd : Odd (num v i1).re := mem_oddSet.1 ((oddSet v).min'_mem h1)
  obtain ⟨i', hi'ne, hi'⟩ := exists_partner hR hU hk1 hi1odd
  have hi'1 : i1 < i' := lt_of_le_of_ne ((oddSet v).min'_le _ (mem_oddSet.2 hi'.2.1))
    (Ne.symm hi'ne)
  have h2 : (partners v i1).Nonempty := ⟨i', mem_partners.2 ⟨hi'1, hi'⟩⟩
  set i2 := (partners v i1).min' h2 with hi2
  have hi2m := mem_partners.1 ((partners v i1).min'_mem h2)
  set z : Fin n := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) (pj s hp).2⟩ with hz
  have hz1le : z ≤ i1 := Fin.le_def.2 (Nat.zero_le _)
  have hz2 : z < i2 := lt_of_le_of_lt hz1le hi2m.1
  refine ⟨i1, i2, z, hz2, rfl, hz1le, hi2m.1, pcol_low hp (ne_zero_of_odd hR hi1odd),
    pcol_low hp (ne_zero_of_odd hR hi2m.2.2.1), hi1odd, hi2m.2, fun i hi => ?_, fun i hi hs' => ?_, ?_⟩
  · exact (oddSet v).min'_le _ (mem_oddSet.2 hi)
  · exact (partners v i1).min'_le _ (mem_partners.2 ⟨hi, hs'⟩)
  · rw [syl_eq_sylOf hp, sylOf_pos hk h1 h2 z hz hz2]

/-- Main Cases 5–8: `G = (-1)_[0]`. -/
theorem main_Z {s : O n} (hs : s ≠ 1) (hn : 0 < n)
    (hr : sem n (Gen.Z ⟨0, hn⟩) * s ≠ 1) : MainSquare s (Gen.Z ⟨0, hn⟩) := by
  classical
  have hp := piv_pos hs
  set z : Fin n := ⟨0, hn⟩ with hzdef
  set j := pj s hp with hj
  set v := col s j with hv
  have hR : InRing v := col_inRing s j
  have hU : IsUnitVec v := col_unit s j
  have hzJ : (z : ℕ) < piv s := hp
  have hz0 : (z : ℕ) = 0 := rfl
  have hzidx : ∀ i ∈ (Gen.Z z).idx, (i : ℕ) < piv s := fun i hi => by
    simp [Gen.idx] at hi; subst hi; exact hzJ
  by_cases hk : lde v = 0
  · obtain ⟨a, ε, hε, hva, haj, hajε⟩ := pcol_single hp hk
    simp only [← hj, ← hv] at hva haj hajε
    have hsyl : syl s = (if hlt : a < j then FreeMonoid.of (Gen.X a j hlt) else 1) *
        (if ε < 0 then FreeMonoid.of (Gen.Z a) else 1) := by
      rw [syl_eq_sylOf hp, ← hj, ← hv, sylOf_zero hk hε hva]
    have ht := piv_t_lt hs hk
    by_cases ha : a = z
    · subst ha
      by_cases hjz : j = z
      · -- `N = (-1)_[0] = G` (Main Case 7, `a = 1`)
        apply square_pro hs
        rw [hsyl, hajε hjz.symm, dif_neg (by rw [hjz]; exact lt_irrefl _), if_pos (by norm_num),
          one_mul]
      · -- `N = X_[0,j] (-1)_[0]^τ` (Main Case 8, `a = 1`): `G N` is the syllable of `G s`
        have hzj : z < j := lt_of_le_of_ne haj (Ne.symm hjz)
        have hcol : gv (Gen.Z z) v = Pi.single z (-ε) := by
          rw [hva]; funext i; simp only [gv, zv]
          split_ifs with h
          · subst h; simp
          · simp [h]
        have hpiv : piv (sem n (Gen.Z z) * s) = piv s := by
          apply piv_eq_of_col hp hzidx
          rw [← hj, ← hv, hcol]
          intro h
          have := congrFun h z
          simp [Ne.symm hjz] at this
          rcases hε with rfl | rfl <;> simp_all
        have hsylr : syl (sem n (Gen.Z z) * s) =
            FreeMonoid.of (Gen.X z j hzj) * (if -ε < 0 then FreeMonoid.of (Gen.Z z) else 1) := by
          rw [syl_of_piv_eq hp hpiv, ← hj, ← hv, hcol,
            sylOf_zero (by rw [← hcol, show gv (Gen.Z z) v = zv z v from rfl, lde_zv z hR]; exact hk)
              (by rcases hε with rfl | rfl <;> simp) rfl, dif_pos hzj]
        refine square_of hs hr [] (lev_syl_lt hs) ?_
        rw [hsylr, hsyl, dif_pos hzj]
        rcases hε with rfl | rfl
        · rw [if_pos (by norm_num), if_neg (by norm_num)]
          show Derivable Fig6 (ofList [Gen.X z j hzj, Gen.Z z, Gen.Z z]) (ofList [Gen.X z j hzj])
          exact rw_at _ 1 (rl_a1 z) rfl
        · rw [if_neg (by norm_num), if_pos (by norm_num)]
          exact Derivable.refl _
    · -- `a > 0`: the syllable stays, and `G` commutes with it (Main Cases 7, 8, `a > 1`)
      have hza : z < a := lt_of_le_of_ne (Fin.le_def.2 (Nat.zero_le _)) (Ne.symm ha)
      have hcol : gv (Gen.Z z) v = v := by
        rw [hva]; funext i; simp only [gv, zv]
        split_ifs with h
        · subst h; simp [Ne.symm ha]
        · rfl
      have hpiv : piv (sem n (Gen.Z z) * s) = piv s := by
        apply piv_eq_of_col hp hzidx
        rw [← hj, ← hv, hcol]
        exact not_fixed_pj hp
      have hsylr : syl (sem n (Gen.Z z) * s) = syl s := by
        rw [syl_of_piv_eq hp hpiv, ← hj, ← hv, hcol, syl_eq_sylOf hp]
      have hJ2 : 1 < piv s := by
        have h1 := Fin.lt_def.1 hza; have h2 := Fin.le_def.1 haj
        rw [hj, pj_val] at h2; omega
      refine square_of hs hr [Gen.Z z] (piv_path (B := piv s - 1) (by omega) [Gen.Z z] _
        (fun g hg i hi => by
          simp at hg; subst hg; simp [Gen.idx] at hi; subst hi; omega)
        (by omega)) ?_
      rw [hsylr, hsyl]
      have hzj : z ≠ j := fun h => by rw [← h] at haj; exact absurd haj (not_le.2 hza)
      split_ifs with hlt hneg hneg
      · show Derivable Fig6 (ofList [Gen.X a j hlt, Gen.Z a, Gen.Z z])
          (ofList [Gen.Z z, Gen.X a j hlt, Gen.Z a])
        exact (rw_at _ 1 (rl_b1 ha) rfl).trans (rw_at _ 0 (rl_b2 hlt (Ne.symm ha) hzj).symm rfl)
      · show Derivable Fig6 (ofList [Gen.X a j hlt, Gen.Z z]) (ofList [Gen.Z z, Gen.X a j hlt])
        exact rw_at _ 0 (rl_b2 hlt (Ne.symm ha) hzj).symm rfl
      · show Derivable Fig6 (ofList [Gen.Z a, Gen.Z z]) (ofList [Gen.Z z, Gen.Z a])
        exact rl_b1 ha
      · show Derivable Fig6 (ofList [Gen.Z z]) (ofList [Gen.Z z])
        exact Derivable.refl _
  · -- a positive exponent: the syllable stays (Main Cases 5, 6)
    obtain ⟨i1, i2, z', hz2, hz', hz1le, h12, hi1J, hi2J, hodd1, hsame, -, -, hsyl⟩ :=
      syl_pos_form hs hk
    have hzz : z' = z := Fin.ext hz'
    subst hzz
    have hJ2 : 1 < piv s := by have := Fin.lt_def.1 hz2; omega
    have hjz : j ≠ z := fun h => by rw [Fin.ext_iff, pj_val] at h; simp [z] at h; omega
    have hpiv : piv (sem n (Gen.Z z) * s) = piv s := by
      apply piv_eq_of_col hp hzidx
      rw [← hj, ← hv]
      intro h
      have h1 : v j = 1 := by
        have := congrFun h j
        simp only [gv, zv, if_neg hjz, Pi.single_eq_same] at this
        exact this
      exact not_fixed_pj hp (eq_single_of_one hU h1)
    have hsylr : syl (sem n (Gen.Z z) * s) = syl s := by
      rw [syl_of_piv_eq hp hpiv, ← hj, ← hv, show gv (Gen.Z z) v = zv z v from rfl,
        sylOf_zv hR hk, syl_eq_sylOf hp]
    have hlev0 : ∀ q : Fin n, (q : ℕ) < piv s → lev0 q < lev s := fun q hq =>
      lev0_lt_of_lde hp hq hk
    by_cases hz1 : z < i1
    · -- `N = H_[0,i₂] X_[0,i₁]` (Main Case 6): `G' = (-1)_[i₁]`
      refine square_of hs hr [Gen.Z i1] (xz_path _ _ (fun g hg => by
          simp at hg; subst hg; exact Or.inr ⟨i1, rfl, hlev0 i1 hi1J⟩) (lev_syl_lt hs)) ?_
      rw [hsylr, hsyl, dif_pos hz1]
      show Derivable Fig6 (ofList [Gen.H z i2 hz2, Gen.X z i1 hz1, Gen.Z z])
        (ofList [Gen.Z i1, Gen.H z i2 hz2, Gen.X z i1 hz1])
      exact (rw_at _ 1 (rl_XZa hz1) rfl).trans
        (rw_at _ 0 (rl_b4 hz2 (ne_of_gt hz1) (ne_of_lt h12)).symm rfl)
    · -- `N = H_[0,i₂]` (Main Case 5): `G' = (-1)_[0] (-1)_[i₂] X_[0,i₂]`
      refine square_of hs hr [Gen.Z z, Gen.Z i2, Gen.X z i2 hz2] (xz_path _ _ (fun g hg => by
          simp at hg
          rcases hg with rfl | rfl | rfl
          · exact Or.inr ⟨z, rfl, hlev0 z hzJ⟩
          · exact Or.inr ⟨i2, rfl, hlev0 i2 hi2J⟩
          · exact Or.inl ⟨z, i2, hz2, rfl, hlev0 i2 hi2J⟩) (lev_syl_lt hs)) ?_
      rw [hsylr, hsyl, dif_neg hz1]
      show Derivable Fig6 (ofList [Gen.H z i2 hz2, Gen.Z z])
        (ofList [Gen.Z z, Gen.Z i2, Gen.X z i2 hz2, Gen.H z i2 hz2])
      exact rl_HZa hz2

end CaseZ

/-! ### `G = X_[0,x]`: Main Cases 1–4 -/

section CaseX

/-- A one-letter path `X_[0,y]` from `t`, below the pivot index of `s`. -/
theorem path_X1 {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) = 0)
    {z y : Fin n} (hzy : z < y) (hy : y < pj s (piv_pos hs)) :
    PathLt (lev s) [Gen.X z y hzy] (FreeMonoid.lift (sem n) (syl s) * s) := by
  have ht := piv_t_lt hs hk
  have hy' := Fin.lt_def.1 hy
  rw [pj_val] at hy'
  have hzy' := Fin.lt_def.1 hzy
  exact piv_path (B := piv s - 1) (by omega) _ _ (fun g hg i hi => by
    simp at hg; subst hg; simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> omega) (by omega)

/-- Main Cases 3 and 4 and the retrograde cases of 1 and 2; Main Cases 1 and 2
proper (below the pivot at a positive exponent) are the hypothesis `hodd`. -/
theorem main_X {s : O n} (hs : s ≠ 1) {z x : Fin n} (hzx : z < x) (hz : (z : ℕ) = 0)
    (hr : sem n (Gen.X z x hzx) * s ≠ 1)
    (hodd : (x : ℕ) < piv s → lde (col s (pj s (piv_pos hs))) ≠ 0 → MainSquare s (Gen.X z x hzx)) :
    MainSquare s (Gen.X z x hzx) := by
  classical
  have hp := piv_pos hs
  -- `x` at or above the pivot: the square is retrograde
  by_cases hxJ : piv s ≤ x
  · exact square_retro hs (syl_X_above hzx hz hxJ)
  push Not at hxJ
  by_cases hk : lde (col s (pj s hp)) ≠ 0
  · exact hodd hxJ hk
  push Not at hk
  have hidx : ∀ i ∈ (Gen.X z x hzx).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi
    rcases hi with rfl | rfl
    · exact lt_trans (Fin.lt_def.1 hzx) hxJ
    · exact hxJ
  obtain ⟨a, ε, hε, hva, haj, hajε⟩ := pcol_single hp hk
  have hsyl := syl_s_single hp hε hva
  have hcolr : gv (Gen.X z x hzx) (col s (pj s hp)) = Pi.single (Equiv.swap z x a) ε := by
    rw [hva]; exact xv_single z x a ε
  have hxj : x ≤ pj s hp := by rw [Fin.le_def, pj_val]; omega
  have hz0 : ∀ i : Fin n, z ≤ i := fun i => Fin.le_def.2 (by omega)
  by_cases ha : a = z
  · rw [ha] at hva hsyl hcolr haj hajε
    have hb : Equiv.swap z x z = x := Equiv.swap_apply_left z x
    rw [hb] at hcolr
    rcases lt_or_eq_of_le hxj with hxj' | hxj'
    · -- Main Case 4 (1): `X_[x,j] (-1)_[x]^τ` from `G s`; `G' = X_[0,x]`
      have hsylr := syl_r_single hp hidx hε hcolr (fun h => absurd h.1 (ne_of_lt hxj'))
      have hzj : z < pj s hp := lt_trans hzx hxj'
      refine square_of hs hr [Gen.X z x hzx] (path_X1 hs hk hzx hxj') ?_
      rw [hsylr, hsyl, dif_pos hxj', dif_pos hzj]
      rcases hε with rfl | rfl
      · rw [if_neg (by norm_num), if_neg (by norm_num)]
        show Derivable Fig6 (ofList [Gen.X x _ hxj', Gen.X z x hzx])
          (ofList [Gen.X z x hzx, Gen.X z _ hzj])
        exact rl_c2 hzx hxj'
      · rw [if_pos (by norm_num), if_pos (by norm_num)]
        show Derivable Fig6 (ofList [Gen.X x _ hxj', Gen.Z x, Gen.X z x hzx])
          (ofList [Gen.X z x hzx, Gen.X z _ hzj, Gen.Z z])
        exact (rw_at _ 1 (rl_XZa hzx).symm rfl).trans (rw_at _ 0 (rl_c2 hzx hxj') rfl)
    · -- Main Case 4 (2): `x = j`
      have hzj : z < pj s hp := hxj' ▸ hzx
      have e1 : Gen.X z (pj s hp) hzj = Gen.X z x hzx := by congr 1; exact hxj'.symm
      rcases hε with rfl | rfl
      · -- `N = X_[0,j] = G`
        apply square_pro hs
        rw [hsyl, dif_pos hzj, if_neg (by norm_num), mul_one, e1]
      · have hsylr := syl_r_single hp hidx (Or.inr rfl) hcolr (fun h => by norm_num at h)
        refine square_of hs hr [] (lev_syl_lt hs) ?_
        rw [hsylr, hsyl, dif_neg (by rw [hxj']; exact lt_irrefl _), dif_pos hzj,
          if_pos (by norm_num), if_pos (by norm_num), one_mul, e1]
        show Derivable Fig6 (ofList [Gen.Z x, Gen.X z x hzx]) (ofList [Gen.X z x hzx, Gen.Z z])
        exact (rl_XZa hzx).symm
  · have hza : z < a := lt_of_le_of_ne (hz0 a) (Ne.symm ha)
    by_cases hxa : x = a
    · -- `x = a`: the column becomes `ε e_0` (Main Cases 3 (2), 4 (4))
      subst hxa
      have hb : Equiv.swap z x x = z := Equiv.swap_apply_right z x
      rw [hb] at hcolr
      have hzj : z < pj s hp := lt_of_lt_of_le hzx haj
      have hsylr := syl_r_single hp hidx hε hcolr (fun h => absurd h.1 (ne_of_lt hzj))
      rcases lt_or_eq_of_le haj with hxj' | hxj'
      · refine square_of hs hr [Gen.X z x hzx] (path_X1 hs hk hzx hxj') ?_
        rw [hsylr, hsyl, dif_pos hzj, dif_pos hxj']
        rcases hε with rfl | rfl
        · rw [if_neg (by norm_num), if_neg (by norm_num)]
          show Derivable Fig6 (ofList [Gen.X z _ hzj, Gen.X z x hzx])
            (ofList [Gen.X z x hzx, Gen.X x _ hxj'])
          exact (rw_at _ 0 (rl_a2 hzx).symm rfl).trans <|
            (rw_at _ 1 (rl_c2 hzx hxj').symm rfl).trans (rw_at _ 2 (rl_a2 hzx) rfl)
        · rw [if_pos (by norm_num), if_pos (by norm_num)]
          show Derivable Fig6 (ofList [Gen.X z _ hzj, Gen.Z z, Gen.X z x hzx])
            (ofList [Gen.X z x hzx, Gen.X x _ hxj', Gen.Z x])
          exact (rw_at _ 1 (rl_c1 hzx) rfl).trans <|
            (rw_at _ 0 (rl_a2 hzx).symm rfl).trans <|
            (rw_at _ 1 (rl_c2 hzx hxj').symm rfl).trans (rw_at _ 2 (rl_a2 hzx) rfl)
      · -- `x = a = j`: `N = (-1)_[j]` (Main Case 3 (2))
        have hε' := hajε hxj'
        subst hε'
        refine square_of hs hr [] (lev_syl_lt hs) ?_
        rw [hsylr, hsyl, dif_pos hzj, dif_neg (by rw [hxj']; exact lt_irrefl _),
          if_pos (by norm_num), if_pos (by norm_num), one_mul]
        have e1 : Gen.X z (pj s hp) hzj = Gen.X z x hzx := by congr 1; exact hxj'.symm
        rw [e1]
        show Derivable Fig6 (ofList [Gen.X z x hzx, Gen.Z z, Gen.X z x hzx]) (ofList [Gen.Z x])
        exact (rw_at _ 1 (rl_c1 hzx) rfl).trans (rw_at _ 0 (rl_a2 hzx) rfl)
    · -- `x ≠ a`: the column stays (Main Cases 3 (1), 4 (3))
      have hb : Equiv.swap z x a = a := Equiv.swap_apply_of_ne_of_ne ha (Ne.symm hxa)
      rw [hb] at hcolr
      have hsylr : syl (sem n (Gen.X z x hzx) * s) = syl s := by
        rw [syl_r_single hp hidx hε hcolr (fun h => not_fixed_pj hp (by
          show col s (pj s hp) = Pi.single (pj s hp) 1
          rw [hva, h.1, h.2])), hsyl]
      rcases lt_or_eq_of_le hxj with hxj' | hxj'
      · -- `G' = X_[0,x]`, commuting with `N`
        refine square_of hs hr [Gen.X z x hzx] (path_X1 hs hk hzx hxj') ?_
        rw [hsylr, hsyl]
        have hxj'' : x ≠ pj s hp := ne_of_lt hxj'
        have hzj : z ≠ pj s hp := ne_of_lt (lt_of_lt_of_le hzx hxj)
        split_ifs with hlt hneg hneg
        · show Derivable Fig6 (ofList [Gen.X a _ hlt, Gen.Z a, Gen.X z x hzx])
            (ofList [Gen.X z x hzx, Gen.X a _ hlt, Gen.Z a])
          exact (rw_at _ 1 (rl_b2 hzx ha (Ne.symm hxa)) rfl).trans
            (rw_at _ 0 (rl_b3 hlt hzx ha (Ne.symm hxa) (Ne.symm hzj) (Ne.symm hxj'')) rfl)
        · show Derivable Fig6 (ofList [Gen.X a _ hlt, Gen.X z x hzx])
            (ofList [Gen.X z x hzx, Gen.X a _ hlt])
          exact rl_b3 hlt hzx ha (Ne.symm hxa) (Ne.symm hzj) (Ne.symm hxj'')
        · show Derivable Fig6 (ofList [Gen.Z a, Gen.X z x hzx]) (ofList [Gen.X z x hzx, Gen.Z a])
          exact rl_b2 hzx ha (Ne.symm hxa)
        · exfalso
          have := hajε (le_antisymm haj (not_lt.1 hlt))
          rw [this] at hneg; norm_num at hneg
      · -- `x = j`: `G' = X_[0,a]`
        have haj' : a < pj s hp := lt_of_le_of_ne haj (fun h => hxa (hxj'.trans h.symm))
        refine square_of hs hr [Gen.X z a hza] (path_X1 hs hk hza haj') ?_
        rw [hsylr, hsyl, dif_pos haj']
        have hax : a < x := hxj' ▸ haj'
        have e2 : Gen.X a (pj s hp) haj' = Gen.X a x hax := by congr 1; exact hxj'.symm
        rw [e2]
        rcases hε with rfl | rfl
        · rw [if_neg (by norm_num)]
          show Derivable Fig6 (ofList [Gen.X a x hax, Gen.X z x hzx])
            (ofList [Gen.X z a hza, Gen.X a x hax])
          exact (rw_at _ 2 (rl_a2 hax).symm rfl).trans <|
            (rw_at _ 1 (rl_c3 hza hax) rfl).trans (rw_at _ 0 (rl_a2 hax) rfl)
        · rw [if_pos (by norm_num)]
          show Derivable Fig6 (ofList [Gen.X a x hax, Gen.Z a, Gen.X z x hzx])
            (ofList [Gen.X z a hza, Gen.X a x hax, Gen.Z a])
          exact (rw_at _ 1 (rl_b2 hzx ha (Ne.symm hxa)) rfl).trans <|
            (rw_at _ 2 (rl_a2 hax).symm rfl).trans <|
            (rw_at _ 1 (rl_c3 hza hax) rfl).trans (rw_at _ 0 (rl_a2 hax) rfl)

end CaseX

/-! ### Main Case 10 -/

section Case10

/-- An odd numerator at exponent `K + 1` rules out exponent `K`. -/
theorem not_den_of_odd {K : ℕ} {x : ℝ} {u : ℤ√2} (h : toReal u = Real.sqrt 2 ^ (K + 1) * x)
    (hodd : Odd u.re) : ¬Den K x := by
  rintro ⟨u0, h0⟩
  have : u = rt2 * u0 := toReal_injective (by
    rw [h, map_mul, toReal_rt2, h0, pow_succ]; ring)
  rw [this] at hodd
  exact Int.not_odd_iff_even.2 (even_re_rt2_mul u0) hodd

/-- With `0`, `1` the first two indices: if entry `0` is odd and `1` is odd of
the same class, the syllable is `H_[0,1]`. -/
theorem sylOf_H01 {j z o : Fin n} {w : Fin n → ℝ} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (hk : lde w ≠ 0) (hzodd : Odd (num w z).re)
    (hsame : SameOdd (num w z) (num w o)) :
    sylOf j w = FreeMonoid.of (Gen.H z o hzo) := by
  classical
  have h1 : (oddSet w).Nonempty := ⟨z, mem_oddSet.2 hzodd⟩
  have hm1 : (oddSet w).min' h1 = z :=
    le_antisymm ((oddSet w).min'_le z (mem_oddSet.2 hzodd))
      ((oddSet w).le_min' _ _ fun y _ => Fin.le_def.2 (by omega))
  have h2 : (partners w ((oddSet w).min' h1)).Nonempty := ⟨o, by rw [hm1]; exact mem_partners.2 ⟨hzo, hsame⟩⟩
  have hm2 : (partners w ((oddSet w).min' h1)).min' h2 = o := by
    apply le_antisymm ((partners w _).min'_le o (by rw [hm1]; exact mem_partners.2 ⟨hzo, hsame⟩))
    apply (partners w _).le_min'
    intro y hy
    rw [hm1, mem_partners] at hy
    have := Fin.lt_def.1 hy.1
    exact Fin.le_def.2 (by omega)
  rw [sylOf_pos hk h1 h2 z (Fin.ext hz) (by rw [hm2]; exact hzo)]
  generalize hgen : (partners w ((oddSet w).min' h1)).min' h2 = m at *
  subst hm2
  rw [dif_neg (by rw [hm1]; exact lt_irrefl _), mul_one]

/-- `H_[0,1]` on an even entry `0` and an odd entry `1`: both become odd of the
same class at exponent `k + 1`. -/
theorem hv_odd_sum {v : Fin n → ℝ} (hR : InRing v) {z o : Fin n} (hzo : z ≠ o)
    (hsum : Odd ((num v z).re + (num v o).re)) :
    lde (hv z o v) ≠ 0 ∧ Odd (num (hv z o v) z).re ∧ SameOdd (num (hv z o v) z) (num (hv z o v) o) := by
  classical
  set k := lde v
  have hz' := toReal_num hR z
  have ho' := toReal_num hR o
  set u : Fin n → ℤ√2 := fun i =>
    if i = z then num v z + num v o else if i = o then num v z - num v o else rt2 * num v i
  have hu : ∀ i, toReal (u i) = Real.sqrt 2 ^ (k + 1) * hv z o v i := by
    intro i
    simp only [u, hv]
    split_ifs with h1 h2
    · exact den_hsum hz' ho'
    · exact den_hdiff hz' ho'
    · rw [map_mul, toReal_rt2, toReal_num hR i, pow_succ]; ring
  have hR' : InRing (hv z o v) := fun i => by
    simp only [hv]
    split_ifs
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.add_mem (hR z) (hR o))
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.sub_mem (hR z) (hR o))
    · exact hR i
  have huz : u z = num v z + num v o := by simp [u]
  have huo : u o = num v z - num v o := by simp [u, Ne.symm hzo]
  have hzodd : Odd (u z).re := by rw [huz, Zsqrtd.re_add]; exact hsum
  have hl : lde (hv z o v) = k + 1 := by
    apply le_antisymm (lde_le fun i => ⟨u i, hu i⟩)
    by_contra hlt
    have := (denV_lde hR').mono (k := lde (hv z o v)) (k' := k) (by omega) z
    exact not_den_of_odd (hu z) hzodd this
  have hnum : num (hv z o v) = u := num_eq hR' (by rw [hl]; exact hu)
  refine ⟨by omega, by rw [hnum]; exact hzodd, ?_⟩
  rw [hnum]
  refine ⟨hzodd, ?_, ?_⟩
  · rw [huo, Zsqrtd.re_sub,
      show (num v z).re - (num v o).re = (num v z).re + (num v o).re - 2 * (num v o).re by ring]
    exact hsum.sub_even (even_two_mul _)
  · rw [huz, huo, Zsqrtd.im_add, Zsqrtd.im_sub,
      show (num v z).im - (num v o).im = (num v z).im + (num v o).im - 2 * (num v o).im by ring]
    exact ⟨fun h => h.sub_even (even_two_mul _), fun h => by
      have := h.add_even (even_two_mul (num v o).im); rwa [sub_add_cancel] at this⟩

/-- `H_[0,1]` on two even entries: the exponent stays, the other numerators
stay, and the two new entries have the same residue. -/
theorem hv_even_even {v : Fin n → ℝ} (hR : InRing v) (hk : lde v ≠ 0) {z o : Fin n} (hzo : z ≠ o)
    (hz : ¬Odd (num v z).re) (ho : ¬Odd (num v o).re) (hodd : ∃ i, Odd (num v i).re) :
    InRing (hv z o v) ∧ lde (hv z o v) = lde v ∧
      (∀ i, i ≠ z → i ≠ o → num (hv z o v) i = num v i) ∧
      (Odd (num (hv z o v) z).re ↔ Odd (num (hv z o v) o).re) ∧
      (Odd (num (hv z o v) z).re → SameOdd (num (hv z o v) z) (num (hv z o v) o)) := by
  classical
  obtain ⟨k1, hk1⟩ : ∃ k1, lde v = k1 + 1 := ⟨lde v - 1, by omega⟩
  -- the two even numerators are `√2` times `w_z`, `w_o`
  obtain ⟨cz, hcz⟩ := Int.not_odd_iff_even.1 hz
  obtain ⟨co, hco⟩ := Int.not_odd_iff_even.1 ho
  set wz : ℤ√2 := ⟨(num v z).im, cz⟩
  set wo : ℤ√2 := ⟨(num v o).im, co⟩
  have hwz : num v z = rt2 * wz := by rw [rt2_mul]; ext <;> simp [wz, hcz]; ring
  have hwo : num v o = rt2 * wo := by rw [rt2_mul]; ext <;> simp [wo, hco]; ring
  have hz' := toReal_num hR z
  have ho' := toReal_num hR o
  rw [hk1] at hz' ho'
  have hz'' : toReal wz = Real.sqrt 2 ^ k1 * v z := by
    rw [hwz, map_mul, toReal_rt2, pow_succ] at hz'
    apply mul_left_cancel₀ sqrt2_ne_zero; rw [hz']; ring
  have ho'' : toReal wo = Real.sqrt 2 ^ k1 * v o := by
    rw [hwo, map_mul, toReal_rt2, pow_succ] at ho'
    apply mul_left_cancel₀ sqrt2_ne_zero; rw [ho']; ring
  set u : Fin n → ℤ√2 := fun i =>
    if i = z then wz + wo else if i = o then wz - wo else num v i
  have hu : ∀ i, toReal (u i) = Real.sqrt 2 ^ (k1 + 1) * hv z o v i := by
    intro i
    simp only [u, hv]
    split_ifs with h1 h2
    · exact den_hsum hz'' ho''
    · exact den_hdiff hz'' ho''
    · rw [← hk1]; exact toReal_num hR i
  have hR' : InRing (hv z o v) := fun i => by
    simp only [hv]
    split_ifs
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.add_mem (hR z) (hR o))
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.sub_mem (hR z) (hR o))
    · exact hR i
  obtain ⟨i0, hi0⟩ := hodd
  have hi0z : i0 ≠ z := fun h => hz (h ▸ hi0)
  have hi0o : i0 ≠ o := fun h => ho (h ▸ hi0)
  have hl : lde (hv z o v) = lde v := by
    rw [hk1]
    apply le_antisymm (lde_le fun i => ⟨u i, hu i⟩)
    by_contra hlt
    have := (denV_lde hR').mono (k := lde (hv z o v)) (k' := k1) (by omega) i0
    refine not_den_of_odd (hu i0) ?_ this
    simp only [u, if_neg hi0z, if_neg hi0o]; exact hi0
  have hnum : num (hv z o v) = u := num_eq hR' (by rw [hl, hk1]; exact hu)
  have huz : u z = wz + wo := by simp [u]
  have huo : u o = wz - wo := by simp [u, Ne.symm hzo]
  refine ⟨hR', hl, fun i h1 h2 => by rw [hnum]; simp [u, h1, h2], ?_, ?_⟩
  · rw [hnum, huz, huo, Zsqrtd.re_add, Zsqrtd.re_sub,
      show wz.re - wo.re = wz.re + wo.re - 2 * wo.re by ring]
    exact ⟨fun h => h.sub_even (even_two_mul _), fun h => by
      have := h.add_even (even_two_mul wo.re); rwa [sub_add_cancel] at this⟩
  · intro h
    rw [hnum, huz] at h
    rw [hnum, huz, huo]
    rw [Zsqrtd.re_add] at h
    refine ⟨by rw [Zsqrtd.re_add]; exact h, ?_, ?_⟩
    · rw [Zsqrtd.re_sub, show wz.re - wo.re = wz.re + wo.re - 2 * wo.re by ring]
      exact h.sub_even (even_two_mul _)
    · rw [Zsqrtd.im_add, Zsqrtd.im_sub, show wz.im - wo.im = wz.im + wo.im - 2 * wo.im by ring]
      exact ⟨fun h' => h'.sub_even (even_two_mul _), fun h' => by
        have := h'.add_even (even_two_mul wo.im); rwa [sub_add_cancel] at this⟩

/-- `H_[p,q]` on two odd entries of the same class strictly lowers the
level. -/
theorem lev_pair_lt {u : O n} (hp : 0 < piv u) {p q : Fin n} (hpq : p < q)
    (hq : (q : ℕ) < piv u) (hk : lde (col u (pj u hp)) ≠ 0)
    (hs : SameOdd (num (col u (pj u hp)) p) (num (col u (pj u hp)) q)) :
    lev (sem n (Gen.H p q hpq) * u) < lev u := by
  have hb : ∀ i ∈ (Gen.H p q hpq).idx, (i : ℕ) < piv u := fun i hi => by
    simp [Gen.idx] at hi; rcases hi with rfl | rfl
    · exact lt_trans (Fin.lt_def.1 hpq) hq
    · exact hq
  have hle := piv_le_of_idx (le_refl (piv u)) hb
  rcases lt_or_eq_of_le hle with h | h
  · exact lev_lt_of_piv_lt h
  · have hpc := pcol_of_piv_eq (w := FreeMonoid.of (Gen.H p q hpq)) (by simpa using h) hp
    simp only [FreeMonoid.lift_eval_of, wv_of, gv] at hpc
    obtain ⟨-, hle', heq⟩ := pair_reduce (col_inRing u _) (ne_of_lt hpq) hs
    apply lev_lt_iff.2; right
    refine ⟨h, ?_⟩
    rw [hpc, pcol_eq hp]
    apply kl_lt_iff.2
    rcases lt_or_eq_of_le hle' with hl | hl
    · left; exact hl
    · right; refine ⟨hl, ?_⟩
      have := heq hl
      rw [hl, if_neg hk, if_neg hk]
      omega

end Case10

/-! ### `G = H_[0,1]`: Main Cases 9–12 -/

section CaseH

/-- `H_[a,c] X_[a,b] ≈ X_[a,b] H_[b,c]` for `a < b < c`, by (c4) and (a2). -/
theorem rl_HX {a b c : Fin n} (hab : a < b) (hbc : b < c) :
    Derivable Fig6 (ofList [Gen.H a c (hab.trans hbc), Gen.X a b hab])
      (ofList [Gen.X a b hab, Gen.H b c hbc]) :=
  (rw_at _ 0 (rl_a2 hab).symm rfl).trans <|
    (rw_at _ 1 (Derivable.of (Fig6.c4 hab hbc)).symm rfl).trans (rw_at _ 2 (rl_a2 hab) rfl)

theorem run_eq_of_der {w w' : List (Gen n)} (d : Derivable Fig6 (ofList w) (ofList w'))
    (t : O n) : run w t = run w' t := by
  rw [run, run, derivable_sound fig6_sound d]

theorem kl_eq_of {v w : Fin n → ℝ} (hl : lde w = lde v) (ho : oddSet w = oddSet v) : kl w = kl v := by
  simp only [kl, hl, ho]

/-- Main Case 9, the subcase the paper's proof gets wrong: entries `0` and `1`
of the pivot column odd of different classes (so `H_[0,1]` keeps the level),
with the first syllable `H_[0,i₂]`, `i₂ > 1`.  Not formalized; this is
Clément's Case 3.4 (`QCert/Clement2019`). -/
theorem main_H_case9_hard {s : O n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (hr : sem n (Gen.H z o hzo) * s ≠ 1) (hoJ : (o : ℕ) < piv s)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (h0 : Odd (num (col s (pj s (piv_pos hs))) z).re)
    (h1 : Odd (num (col s (pj s (piv_pos hs))) o).re)
    (hdiff : ¬SameOdd (num (col s (pj s (piv_pos hs))) z) (num (col s (pj s (piv_pos hs))) o)) :
    MainSquare s (Gen.H z o hzo) := by
  sorry

/-- Main Case 9: `G = H_[0,1]` and first syllable `H_[0,i₂]`. -/
theorem main_H_case9 {s : O n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (hr : sem n (Gen.H z o hzo) * s ≠ 1) (hoJ : (o : ℕ) < piv s)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (h0 : Odd (num (col s (pj s (piv_pos hs))) z).re) : MainSquare s (Gen.H z o hzo) := by
  classical
  have hp := piv_pos hs
  obtain ⟨i1, i2, z', hz2, hz', hz1le, h12, hi1J, hi2J, hodd1, hsame, hmin1, hmin2, hsyl⟩ :=
    syl_pos_form hs hk
  have hzz : z' = z := Fin.ext (by rw [hz', hz])
  subst hzz
  have hi1 : i1 = z' := le_antisymm (hmin1 z' h0) hz1le
  subst hi1
  have hsyl' : syl s = FreeMonoid.of (Gen.H i1 i2 hz2) := by
    rw [hsyl, dif_neg (lt_irrefl _), mul_one]
  by_cases hi2 : i2 = o
  · -- Main Case 9 (1): `i₂ = 2`, the square is prograde
    subst hi2
    exact square_pro hs hsyl'
  set v := col s (pj s hp) with hvdef
  have hR : InRing v := col_inRing s _
  have hoi2 : o < i2 := lt_of_le_of_ne (Fin.le_def.2 (by have := Fin.lt_def.1 hz2; omega))
    (Ne.symm hi2)
  by_cases hoodd : Odd (num v o).re
  · -- Main Case 9 (2)(b): both odd; they are of different classes since `i₂ > 1`
    exact main_H_case9_hard hs hzo hz ho hr hoJ hk h0 hoodd
      (fun h => absurd (hmin2 o hzo h) (not_le.2 hoi2))
  · -- Main Case 9 (2)(a): entry `1` even; the square is retrograde
    have hidx : ∀ i ∈ (Gen.H i1 o hzo).idx, (i : ℕ) < piv s := by
      intro i hi; simp [Gen.idx] at hi
      rcases hi with rfl | rfl <;> omega
    obtain ⟨hl, hzodd, hsame'⟩ :=
      hv_odd_sum hR (ne_of_lt hzo) (h0.add_even (Int.not_odd_iff_even.1 hoodd))
    have hpiv : piv (sem n (Gen.H i1 o hzo) * s) = piv s :=
      piv_eq_of_col hp hidx (by
        show hv i1 o v ≠ _
        intro h; rw [h] at hl
        exact hl (lde_eq_zero_of_int fun i => by
          by_cases hi : i = pj s hp
          · subst hi; exact ⟨1, by simp⟩
          · exact ⟨0, by simp [hi]⟩))
    apply square_retro hs
    rw [syl_of_piv_eq hp hpiv, ← hvdef]
    exact sylOf_H01 hzo hz ho hl hzodd hsame'

/-- Main Cases 9 and 10: `G = H_[0,1]` below the pivot at a positive
exponent. -/
theorem main_H_odd {s : O n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (hr : sem n (Gen.H z o hzo) * s ≠ 1) (hoJ : (o : ℕ) < piv s)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) : MainSquare s (Gen.H z o hzo) := by
  classical
  have hp := piv_pos hs
  obtain ⟨i1, i2, z', hz2, hz', hz1le, h12, hi1J, hi2J, hodd1, hsame, hmin1, -, hsyl⟩ :=
    syl_pos_form hs hk
  have hzz : z' = z := Fin.ext (by rw [hz', hz])
  subst hzz
  set v := col s (pj s hp) with hvdef
  have hR : InRing v := col_inRing s _
  by_cases hz1 : z' < i1
  swap
  · -- Main Case 9: the first odd entry is `0`
    have : i1 = z' := le_antisymm (not_lt.1 hz1) hz1le
    exact main_H_case9 hs hzo hz ho hr hoJ hk (this ▸ hodd1)
  -- Main Case 10
  have hzeven : ¬Odd (num v z').re := fun h => absurd (hmin1 z' h) (not_le.2 hz1)
  have hidx : ∀ i ∈ (Gen.H z' o hzo).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi
    rcases hi with rfl | rfl <;> omega
  have hcolr : gv (Gen.H z' o hzo) v = hv z' o v := rfl
  have hpiv_of : lde (hv z' o v) ≠ 0 → piv (sem n (Gen.H z' o hzo) * s) = piv s := fun hl =>
    piv_eq_of_col hp hidx (by
      rw [← hvdef, hcolr]; intro h; rw [h] at hl
      exact hl (lde_eq_zero_of_int fun i => by
        by_cases hi : i = pj s hp
        · subst hi; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [hi]⟩))
  by_cases hio : i1 = o
  · -- Case 10 (1): `i₁ = 1`: the square is retrograde
    have hoodd : Odd (num v o).re := hio ▸ hodd1
    obtain ⟨hl, hzodd, hsame'⟩ :=
      hv_odd_sum hR (ne_of_lt hzo) ((Int.not_odd_iff_even.1 hzeven).add_odd hoodd)
    apply square_retro hs
    rw [syl_of_piv_eq hp (hpiv_of hl), ← hvdef, hcolr, sylOf_H01 hzo hz ho hl hzodd hsame']
  -- Case 10 (2): `i₁ > 1`; entries `0` and `1` are even
  have hoi1 : o < i1 := lt_of_le_of_ne (Fin.le_def.2 (by have := Fin.lt_def.1 hz1; omega))
    (Ne.symm hio)
  have hoeven : ¬Odd (num v o).re := fun h => absurd (hmin1 o h) (not_le.2 hoi1)
  obtain ⟨hR', hl, hsamenum, hpar, hsameo⟩ :=
    hv_even_even hR hk (ne_of_lt hzo) hzeven hoeven ⟨i1, hodd1⟩
  have hl0 : lde (hv z' o v) ≠ 0 := by rw [hl]; exact hk
  have hpiv := hpiv_of hl0
  by_cases hw : Odd (num (hv z' o v) z').re
  · -- the two new entries are odd: retrograde
    apply square_retro hs
    rw [syl_of_piv_eq hp hpiv, ← hvdef, hcolr, sylOf_H01 hzo hz ho hl0 hw (hsameo hw)]
  -- the two new entries are even: the syllable stays
  have hwo : ¬Odd (num (hv z' o v) o).re := fun h => hw (hpar.2 h)
  have hodds : oddSet (hv z' o v) = oddSet v := by
    ext i
    rw [mem_oddSet, mem_oddSet]
    by_cases h1 : i = z'
    · subst h1; exact ⟨fun h => absurd h hw, fun h => absurd h hzeven⟩
    · by_cases h2 : i = o
      · subst h2; exact ⟨fun h => absurd h hwo, fun h => absurd h hoeven⟩
      · rw [hsamenum i h1 h2]
  have hparts : partners (hv z' o v) = partners v := by
    funext i
    ext i'
    rw [mem_partners, mem_partners]
    by_cases hi : i = z' ∨ i = o
    · constructor
      · rintro ⟨-, h, -⟩; rcases hi with rfl | rfl
        · exact absurd h hw
        · exact absurd h hwo
      · rintro ⟨-, h, -⟩; rcases hi with rfl | rfl
        · exact absurd h hzeven
        · exact absurd h hoeven
    · push Not at hi
      rw [hsamenum i hi.1 hi.2]
      by_cases hi' : i' = z' ∨ i' = o
      · constructor
        · rintro ⟨-, -, h, -⟩; rcases hi' with rfl | rfl
          · exact absurd h hw
          · exact absurd h hwo
        · rintro ⟨-, -, h, -⟩; rcases hi' with rfl | rfl
          · exact absurd h hzeven
          · exact absurd h hoeven
      · push Not at hi'
        rw [hsamenum i' hi'.1 hi'.2]
  have hsylr : syl (sem n (Gen.H z' o hzo) * s) = syl s := by
    rw [syl_of_piv_eq hp hpiv, ← hvdef, hcolr, sylOf_eq_sylPos hl0, hodds, hparts,
      syl_eq_sylOf hp, ← hvdef, sylOf_eq_sylPos hk]
  have hs' : syl s = ofList [Gen.H z' i2 hz2, Gen.X z' i1 hz1] := by rw [hsyl, dif_pos hz1]; rfl
  -- the derivation `H_[0,i₂] X_[0,i₁] H_[0,1] ≈ X_[0,i₁] H_[0,1] X_[0,i₁] H_[0,i₂] X_[0,i₁]`
  have hzi1 : z' ≠ i1 := ne_of_lt hz1
  have hb6 := rl_b6 h12 hzo (Ne.symm hzi1) (ne_of_gt hoi1)
    (ne_of_gt (lt_trans hz1 h12)) (ne_of_gt (lt_trans hoi1 h12))
  have hder : Derivable Fig6 (ofList [Gen.H z' i2 hz2, Gen.X z' i1 hz1, Gen.H z' o hzo])
      (ofList [Gen.X z' i1 hz1, Gen.H z' o hzo, Gen.X z' i1 hz1, Gen.H z' i2 hz2,
        Gen.X z' i1 hz1]) :=
    ((rw_at _ 0 (rl_HX hz1 h12) rfl).trans (rw_at _ 1 hb6 rfl)).trans
      ((rw_at [Gen.X z' i1 hz1, Gen.H z' o hzo, Gen.X z' i1 hz1, Gen.H z' i2 hz2,
        Gen.X z' i1 hz1] 3 (rl_HX hz1 h12) rfl).trans (rw_at _ 2 (rl_a2 hz1) rfl)).symm
  -- the states of the path
  have ht : FreeMonoid.lift (sem n) (syl s) * s = run [Gen.H z' i2 hz2, Gen.X z' i1 hz1] s := by
    rw [hs']; rfl
  have hXHX : run [Gen.X z' i1 hz1, Gen.H z' i2 hz2, Gen.X z' i1 hz1] s =
      run [Gen.H i1 i2 h12] s :=
    run_eq_of_der ((rw_at _ 1 (rl_HX hz1 h12) rfl).trans (rw_at _ 0 (rl_a2 hz1) rfl)) s
  have hlev_r : lev (sem n (Gen.H z' o hzo) * s) = lev s := by
    have hpc := pcol_of_piv_eq (w := FreeMonoid.of (Gen.H z' o hzo)) (by simpa using hpiv) hp
    simp only [FreeMonoid.lift_eval_of, wv_of, gv] at hpc
    rw [lev, lev, hpiv, hpc, pcol_eq hp, ← hvdef, kl_eq_of hl hodds]
  have hpr : 0 < piv (sem n (Gen.H z' o hzo) * s) := hpiv ▸ hp
  have hcol_r : col (sem n (Gen.H z' o hzo) * s) (pj _ hpr) = hv z' o v := by
    have : pj _ hpr = pj s hp := Fin.ext (by simp only [pj]; rw [hpiv])
    rw [this, col_sem_mul]
    rfl
  refine square_of hs hr [Gen.X z' i1 hz1, Gen.H z' o hzo, Gen.X z' i1 hz1] ?_ ?_
  · rw [ht]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [← ht]; exact lev_syl_lt hs
    · -- `X_[0,i₁] t = H_[i₁,i₂] s`
      rw [← run_append]
      show lev (run [Gen.X z' i1 hz1, Gen.H z' i2 hz2, Gen.X z' i1 hz1] s) < lev s
      rw [hXHX, run_cons, run_nil]
      exact lev_pair_lt hp h12 hi2J hk hsame
    · -- `H_[0,1] X_[0,i₁] t = H_[i₁,i₂] (H_[0,1] s)`
      rw [← run_append]
      show lev (run [Gen.H z' o hzo, Gen.X z' i1 hz1, Gen.H z' i2 hz2, Gen.X z' i1 hz1] s) < lev s
      rw [show [Gen.H z' o hzo, Gen.X z' i1 hz1, Gen.H z' i2 hz2, Gen.X z' i1 hz1] =
        [Gen.H z' o hzo] ++ [Gen.X z' i1 hz1, Gen.H z' i2 hz2, Gen.X z' i1 hz1] from rfl,
        run_append, hXHX, ← run_append]
      rw [run_eq_of_der (w' := [Gen.H i1 i2 h12, Gen.H z' o hzo]) (rw_at _ 0 hb6.symm rfl),
        run_cons, run_cons, run_nil]
      rw [← hlev_r]
      refine lev_pair_lt hpr h12 (by rw [hpiv]; exact hi2J) (by rw [hcol_r]; exact hl0) ?_
      rw [hcol_r, hsamenum i1 (ne_of_gt hz1) (ne_of_gt hoi1),
        hsamenum i2 (ne_of_gt (lt_trans hz1 h12)) (ne_of_gt (lt_trans hoi1 h12))]
      exact hsame
    · -- the last state is the normal successor of `H_[0,1] s`
      have hsound := derivable_sound fig6_sound hder
      have : run [Gen.X z' i1 hz1, Gen.H z' o hzo, Gen.X z' i1 hz1]
          (run [Gen.H z' i2 hz2, Gen.X z' i1 hz1] s) =
          FreeMonoid.lift (sem n) (syl (sem n (Gen.H z' o hzo) * s)) * (sem n (Gen.H z' o hzo) * s) := by
        rw [← run_append]
        show FreeMonoid.lift (sem n) (ofList [Gen.X z' i1 hz1, Gen.H z' o hzo, Gen.X z' i1 hz1,
          Gen.H z' i2 hz2, Gen.X z' i1 hz1]) * s = _
        rw [← hsound, hsylr, hs']
        show FreeMonoid.lift (sem n) (ofList [Gen.H z' i2 hz2, Gen.X z' i1 hz1] *
          FreeMonoid.of (Gen.H z' o hzo)) * s = _
        rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc]
      rw [this, ← hlev_r]
      exact lev_syl_lt hr
  · rw [hsylr, hs']
    exact hder

theorem hv_single_other {p q a : Fin n} (ε : ℝ) (hap : a ≠ p) (haq : a ≠ q) :
    hv p q (Pi.single a ε) = Pi.single a ε := by
  funext i
  simp only [hv]
  split_ifs with h1 h2
  · subst h1; simp [Ne.symm hap, Ne.symm haq]
  · subst h2; simp [Ne.symm hap, Ne.symm haq]
  · rfl

theorem main_H {s : O n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (hr : sem n (Gen.H z o hzo) * s ≠ 1) : MainSquare s (Gen.H z o hzo) := by
  classical
  have hp := piv_pos hs
  by_cases hoJ : piv s ≤ o
  · exact square_retro hs (syl_H_above hzo hz hoJ)
  push Not at hoJ
  by_cases hk : lde (col s (pj s hp)) ≠ 0
  · exact main_H_odd hs hzo hz ho hr hoJ hk
  push Not at hk
  have hidx : ∀ i ∈ (Gen.H z o hzo).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi
    rcases hi with rfl | rfl <;> omega
  obtain ⟨a, ε, hε, hva, haj, hajε⟩ := pcol_single hp hk
  have hsyl := syl_s_single hp hε hva
  have hoj : o ≤ pj s hp := by rw [Fin.le_def, pj_val]; omega
  by_cases ha : a = z ∨ a = o
  · -- Main Cases 11 (1), 12 (1): the square is retrograde
    apply square_retro hs
    obtain ⟨e, he, rfl⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ε = e := by
      rcases hε with rfl | rfl
      · exact ⟨1, Or.inl rfl, by simp⟩
      · exact ⟨-1, Or.inr rfl, by simp⟩
    have hcolr : gv (Gen.H z o hzo) (col s (pj s hp)) = hv z o (Pi.single a (e : ℝ)) := by
      rw [hva]; rfl
    have hpiv : piv (sem n (Gen.H z o hzo) * s) = piv s := by
      apply piv_eq_of_col hp hidx
      rw [hcolr]
      intro h
      have hj := congrFun h (pj s hp)
      rw [Pi.single_eq_same] at hj
      obtain ⟨hR, hl, hodd, -, hzero⟩ := hv_pm_facts hzo ha he
      by_cases hjo : pj s hp = o
      · -- the entry at `o` is odd at exponent 1, not `1`
        have := toReal_num hR (pj s hp)
        rw [hj, hl, mul_one, pow_one] at this
        have hm : pj s hp ∈ oddSet (hv z o (Pi.single a (e : ℝ))) := by rw [hodd, hjo]; simp
        have h2 : num (hv z o (Pi.single a (e : ℝ))) (pj s hp) = rt2 := by
          apply toReal_injective; rw [this, toReal_rt2]
        rw [mem_oddSet, h2] at hm
        simp [rt2] at hm
      · have hjz : pj s hp ≠ z := fun h' => by
          have := Fin.lt_def.1 hzo; rw [← h'] at this; rw [Fin.le_def] at hoj; omega
        have := toReal_num hR (pj s hp)
        rw [hzero _ hjz hjo, hj, map_zero] at this
        exact absurd this.symm (by simp [sqrt2_ne_zero])
    rw [syl_of_piv_eq hp hpiv, hcolr, sylOf_hv_pm hzo hz ha he]
  · -- Main Cases 11 (2), 12 (2): the column stays and `H_[0,1]` commutes with `N`
    push Not at ha
    have hcolr : gv (Gen.H z o hzo) (col s (pj s hp)) = col s (pj s hp) := by
      rw [hva]; exact hv_single_other ε ha.1 ha.2
    have hpiv : piv (sem n (Gen.H z o hzo) * s) = piv s := by
      apply piv_eq_of_col hp hidx
      rw [hcolr]; exact not_fixed_pj hp
    have hsylr : syl (sem n (Gen.H z o hzo) * s) = syl s := by
      rw [syl_of_piv_eq hp hpiv, hcolr, syl_eq_sylOf hp]
    have hoa : o < a := lt_of_le_of_ne (Fin.le_def.2 (by
      have : (a : ℕ) ≠ 0 := fun h => ha.1 (Fin.ext (by omega))
      have : (a : ℕ) ≠ 1 := fun h => ha.2 (Fin.ext (by omega))
      omega)) (Ne.symm ha.2)
    have hoj' : o < pj s hp := lt_of_lt_of_le hoa haj
    have ht := piv_t_lt hs hk
    have hjv := Fin.lt_def.1 hoj'
    rw [pj_val] at hjv
    refine square_of hs hr [Gen.H z o hzo] (piv_path (B := piv s - 1) (by omega) _ _
      (fun g hg i hi => by
        simp at hg; subst hg; simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> omega)
      (by omega)) ?_
    rw [hsylr, hsyl]
    have hza : z ≠ a := Ne.symm ha.1
    have hzj : z ≠ pj s hp := ne_of_lt (lt_of_lt_of_le hzo hoj)
    have hoj'' : o ≠ pj s hp := ne_of_lt hoj'
    split_ifs with hlt hneg hneg
    · show Derivable Fig6 (ofList [Gen.X a _ hlt, Gen.Z a, Gen.H z o hzo])
        (ofList [Gen.H z o hzo, Gen.X a _ hlt, Gen.Z a])
      exact (rw_at _ 1 (rl_b4 hzo ha.1 ha.2) rfl).trans
        (rw_at _ 0 (rl_b5 hlt hzo ha.1 ha.2 (Ne.symm hzj) (Ne.symm hoj'')) rfl)
    · show Derivable Fig6 (ofList [Gen.X a _ hlt, Gen.H z o hzo])
        (ofList [Gen.H z o hzo, Gen.X a _ hlt])
      exact rl_b5 hlt hzo ha.1 ha.2 (Ne.symm hzj) (Ne.symm hoj'')
    · show Derivable Fig6 (ofList [Gen.Z a, Gen.H z o hzo]) (ofList [Gen.H z o hzo, Gen.Z a])
      exact rl_b4 hzo ha.1 ha.2
    · exfalso
      have := hajε (le_antisymm haj (not_lt.1 hlt))
      rw [this] at hneg; norm_num at hneg

end CaseH

end QCert.HadamardPi
