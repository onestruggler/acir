/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: termination and normal words

Theorem 2.16: the syllable of a state `s ≠ I` lowers its level, so
Algorithm 2.14 terminates.  The normal word of a state (§3.2) is then
defined by well-founded recursion on the level, `nw s = nw (S s) · S` with
`S` the syllable of `s`, and reduces the state to the identity:
`⟦nw s⟧ s = I`.
-/
import QCert.BianSelingerUn.Syllable

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

theorem eq_ev_of_hasNum {v : Fin n → ℂ} {w : Fin n → GaussianInt} (h : HasNum v 0 w) {p : Fin n}
    (hw : ∀ a, w a = if a = p then 1 else 0) : v = ev p := by
  funext a
  have := h a
  rw [pow_zero, one_mul, hw a] at this
  rw [this, ev]; split_ifs <;> simp

theorem prof_lt_of {v v' : Fin n → ℂ} {k : ℕ} {w w' : Fin n → GaussianInt} (hv : HasNum v k w)
    (hk : lde v = k) (hv' : HasNum v' k w') (hlt : (oddSet w').card < (oddSet w).card) :
    prof v' < prof v := by
  rw [prof_eq hv hk]
  rcases (lde_le hv').lt_or_eq with h | h
  · rw [prof, Prod.Lex.toLex_lt_toLex]; left; exact h
  · rw [prof_eq hv' h, Prod.Lex.toLex_lt_toLex]; right; exact ⟨rfl, hlt⟩

theorem hasNum_zero_of_entry {s : St n} {p : Fin n} (hp : IsPivot s p) {k : ℕ}
    {w : Fin n → GaussianInt} (hw : HasNum (col s p) k w) {a : Fin n} (ha : p < a) : w a = 0 := by
  have := hw a
  rw [hp.entry_zero ha, mul_zero, eq_comm, GaussianInt.toComplex_eq_zero] at this
  exact this

theorem not_GOdd_iz_γz (d : GaussianInt) : ¬ GOdd (iz * γz * d) := by
  rw [mul_assoc, GOdd_iz_mul]; exact not_GOdd_γz_mul d

theorem ev_apply_ne {q a : Fin n} (h : a ≠ q) : ev q a = 0 := by simp [ev, h]

/-- Theorem 2.16: the syllable of a state `s ≠ I` lowers its level. -/
theorem level_syl_lt {s : St n} (hs : s ≠ 1) :
    level (FreeMonoid.lift (sem n) (syl s) * s) < level s := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  have hcol : ∀ q, col (FreeMonoid.lift (sem n) (syl s) * s) q = matOf (syl s) *ᵥ col s q := by
    intro q; rw [col_mul, sm_lift]
  rw [syl_eq hp]
  rw [syl_eq hp] at hcol
  obtain ⟨w, hw⟩ := lde_spec (hasNum_exists s p)
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · -- `k = 0`: the pivot column is `i^{-e} e_c` (Corollary 2.8)
    rw [hk] at hw
    have hsum := sum_norm_eq (col_unit s p) hw
    rw [pow_zero] at hsum
    obtain ⟨c, hc1, hc0⟩ := unit_of_sum_norm_one hsum
    have hcne : w c ≠ 0 := by intro h; rw [h] at hc1; simp at hc1
    have hcp : c ≤ p := by
      by_contra h; exact hcne (hasNum_zero_of_entry hp hw (not_le.1 h))
    rcases hcp.lt_or_eq with hcp | rfl
    · rw [sylCol_unit_lt hw hcne hc0 hcp] at hcol ⊢
      apply level_lt_of_cols hp
      · intro q hq
        rw [hcol, hp.2 q hq, matOf_mul_mulVec, matOf_ipow, matOf_X,
          oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt (hcp.trans hq))),
          twoLevel_mulVec_of_zero hcp.ne _ (ev_apply_ne (ne_of_lt (hcp.trans hq)))
            (ev_apply_ne (ne_of_lt hq))]
      · left
        rw [hcol, matOf_mul_mulVec, matOf_ipow, matOf_X]
        apply eq_ev_of_hasNum (hasNum_X (hasNum_oneLevel hw c _) hcp.ne)
        intro a
        rw [iz_pow_expo_mul hc1]
        simp only [Function.update_apply]
        split_ifs <;> simp_all
    · rw [sylCol_unit_eq hw hcne hc0] at hcol ⊢
      apply level_lt_of_cols hp
      · intro q hq
        rw [hcol, hp.2 q hq, matOf_ipow, oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt hq))]
      · left
        rw [hcol, matOf_ipow]
        apply eq_ev_of_hasNum (hasNum_oneLevel hw _ _)
        intro a
        rw [iz_pow_expo_mul hc1]
        simp only [Function.update_apply]
        split_ifs <;> simp_all
  · -- `k > 0`: the row operation on the first two odd entries (Lemma 2.10)
    have hev := even_card_odd (col_unit s p) hw hk
    obtain ⟨j0, hj0⟩ := exists_odd hw hk
    have h2 : 2 ≤ (oddSet w).card := by
      have : 0 < (oddSet w).card := Finset.card_pos.2 ⟨j0, mem_oddSet.2 hj0⟩
      have hev' : Even (oddSet w).card := hev
      obtain ⟨r, hr⟩ := hev'
      omega
    obtain ⟨j, l, hf⟩ := exists_firstTwo h2
    have hlp : l ≤ p := by
      by_contra h
      have := hasNum_zero_of_entry hp hw (not_le.1 h)
      have h3 := hf.2.2.1
      rw [this] at h3; exact absurd h3 (by decide)
    have hjl := hf.1
    rw [sylCol_K hw hk rfl hf] at hcol ⊢
    apply level_lt_of_cols hp
    · intro q hq
      rw [hcol, hp.2 q hq, matOf_mul_mulVec, matOf_ipow, matOf_Kd,
        oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt (lt_of_le_of_lt hlp hq))),
        twoLevel_mulVec_of_zero hjl.ne _ (ev_apply_ne (ne_of_lt ((hjl.trans_le hlp).trans hq)))
          (ev_apply_ne (ne_of_lt (lt_of_le_of_lt hlp hq)))]
    · right
      rw [hcol, matOf_mul_mulVec, matOf_ipow, matOf_Kd]
      have h1 := hasNum_Kd (hasNum_oneLevel hw l (qexp (w j) (w l))) hjl.ne
      obtain ⟨⟨d1, hd1⟩, ⟨d2, hd2⟩⟩ := γz_sq_dvd_add_sub hf.2.1 hf.2.2.1
      let w3 : Fin n → GaussianInt :=
        Function.update (Function.update w j (iz * γz * d1)) l (iz * γz * d2)
      have h3 : HasNum (twoLevel j l Kdmat *ᵥ (oneLevel l (I ^ qexp (w j) (w l)) *ᵥ col s p))
          (lde (col s p)) w3 := by
        obtain ⟨k', hk'⟩ : ∃ k', lde (col s p) = k' + 1 := ⟨lde (col s p) - 1, by omega⟩
        rw [hk'] at h1 ⊢
        apply h1.pred
        intro a
        dsimp only [w3]
        by_cases hal : a = l
        · rw [hal]
          simp only [Function.update_self, Function.update_of_ne hjl.ne]
          rw [hd2]; ring
        · by_cases haj : a = j
          · rw [haj]
            simp only [Function.update_self, Function.update_of_ne hjl.ne]
            rw [hd1]; ring
          · simp only [Function.update_of_ne hal, Function.update_of_ne haj]
      apply prof_lt_of hw rfl h3
      have hsub : oddSet w3 = ((oddSet w).erase l).erase j := by
        ext a
        simp only [mem_oddSet, Finset.mem_erase, w3, Function.update_apply]
        by_cases hal : a = l
        · rw [if_pos hal]; exact iff_of_false (not_GOdd_iz_γz _) (fun h => h.2.1 hal)
        · by_cases haj : a = j
          · rw [if_neg hal, if_pos haj]; exact iff_of_false (not_GOdd_iz_γz _) (fun h => h.1 haj)
          · rw [if_neg hal, if_neg haj]; exact ⟨fun h => ⟨haj, hal, h⟩, fun h => h.2.2⟩
      rw [hsub, Finset.card_erase_of_mem, Finset.card_erase_of_mem (mem_oddSet.2 hf.2.2.1)]
      · omega
      · exact Finset.mem_erase.2 ⟨hjl.ne, mem_oddSet.2 hf.2.1⟩

/-- The relation "smaller level" on states is well founded. -/
theorem wf_level : WellFounded (fun s t : St n => level s < level t) :=
  InvImage.wf level wellFounded_lt

open Classical in
/-- The normal word of a state (§3.2): its syllables down to `I`, the last
one first, so that `⟦nw s⟧ s = I`. -/
def nw : St n → Word (Gen n) :=
  wf_level.fix fun s IH =>
    if h : s = 1 then 1 else IH (FreeMonoid.lift (sem n) (syl s) * s) (level_syl_lt h) * syl s

theorem nw_eq (s : St n) :
    nw s = if s = 1 then 1 else nw (FreeMonoid.lift (sem n) (syl s) * s) * syl s := by
  rw [nw, WellFounded.fix_eq]
  split_ifs <;> rfl

theorem nw_one : nw (1 : St n) = 1 := by rw [nw_eq, if_pos rfl]

theorem nw_of_ne {s : St n} (h : s ≠ 1) :
    nw s = nw (FreeMonoid.lift (sem n) (syl s) * s) * syl s := by
  rw [nw_eq, if_neg h]

/-- The normal word reduces its state to the identity. -/
theorem nw_reduces (s : St n) : FreeMonoid.lift (sem n) (nw s) * s = 1 := by
  induction s using wf_level.induction with
  | _ s ih =>
    by_cases h : s = 1
    · subst h; rw [nw_one, map_one, one_mul]
    · rw [nw_of_ne h, map_mul, mul_assoc]
      exact ih _ (level_syl_lt h)

end

end QCert.BianSelingerUn
