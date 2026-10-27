/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: termination and normal words

Theorem 18: the syllable of a state `s ≠ I` lowers its level (by Lemmas 13
and 14), so Algorithm 16 terminates.  The normal word of a state (§3.3,
Definition 25 and Remark 26) is then defined by well-founded recursion on
the level, `nw s = nw (S s) · S` with `S` the syllable of `s`, and reduces
the state to the identity: `⟦nw s⟧ s = I`.
-/
import QCert.Greylyn.Syllable

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

theorem eq_ev_of_hasNum {v : Fin n → ℂ} {w : Fin n → ZOmega} (h : HasNum v 0 w) {p : Fin n}
    (hw : ∀ a, w a = if a = p then 1 else 0) : v = ev p := by
  funext a
  have := h a
  rw [pow_zero, one_mul, hw a] at this
  rw [this, ev]; split_ifs <;> simp

theorem prof_lt_of {v v' : Fin n → ℂ} {k : ℕ} {w w' : Fin n → ZOmega} (hv : HasNum v k w)
    (hk : lde v = k) (hk0 : 0 < k) (hv' : HasNum v' k w')
    (hlt : (oddSet w').card < (oddSet w).card) : prof v' < prof v := by
  rw [prof_eq hv hk, if_neg (by omega)]
  rcases (lde_le hv').lt_or_eq with h | h
  · rw [prof, Prod.Lex.toLex_lt_toLex]; left; exact h
  · rw [prof_eq hv' h, if_neg (by omega), Prod.Lex.toLex_lt_toLex]; right; exact ⟨rfl, hlt⟩

theorem hasNum_zero_of_entry {s : St n} {p : Fin n} (hp : IsPivot s p) {k : ℕ}
    {w : Fin n → ZOmega} (hw : HasNum (col s p) k w) {a : Fin n} (ha : p < a) : w a = 0 := by
  have := hw a
  rw [hp.entry_zero ha, mul_zero, eq_comm] at this
  exact eq_zero_of_toC this

theorem ev_apply_ne {q a : Fin n} (h : a ≠ q) : ev q a = 0 := by simp [ev, h]

theorem not_isOdd_ηz_δz_mul (d : ZOmega) : ¬ IsOdd (ηz * δz * d) := by
  apply not_isOdd_of_dvd
  exact ⟨ηz * d, by ring⟩

/-- Theorem 18, column by column: the syllable of a state with pivot `p`
fixes the columns beyond `p`, and makes column `p` equal to `eₚ` when its
least δ-exponent is `0` and lowers its profile otherwise. -/
theorem syl_cols {s : St n} {p : Fin n} (hp : IsPivot s p) :
    (∀ q, p < q → col (FreeMonoid.lift (sem n) (syl s) * s) q = ev q) ∧
      (lde (col s p) = 0 → col (FreeMonoid.lift (sem n) (syl s) * s) p = ev p) ∧
      (0 < lde (col s p) →
        prof (col (FreeMonoid.lift (sem n) (syl s) * s) p) < prof (col s p)) := by
  have hcol : ∀ q, col (FreeMonoid.lift (sem n) (syl s) * s) q = matOf (syl s) *ᵥ col s q := by
    intro q; rw [col_mul, sm_lift]
  rw [syl_eq hp]
  rw [syl_eq hp] at hcol
  obtain ⟨w, hw⟩ := lde_spec (hasNum_exists s p)
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · -- `k = 0`: the pivot column is `ωᵐ e_c` (Lemma 14, Lemma 15)
    rw [hk] at hw
    obtain ⟨c, hc1, hc0⟩ := unit_of_sum (col_unit s p) hw
    have hcne : w c ≠ 0 := by intro h; rw [h] at hc1; simp [nrm0] at hc1
    have hcp : c ≤ p := by
      by_contra h; exact hcne (hasNum_zero_of_entry hp hw (not_le.1 h))
    rcases hcp.lt_or_eq with hcp | hcp
    · rw [sylCol_unit_lt hw hcne hc0 hcp] at hcol ⊢
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        rw [hcol, hp.2 q hq, matOf_mul_mulVec, matOf_ωpow, matOf_X,
          twoLevel_mulVec_of_zero hcp.ne _ (ev_apply_ne (ne_of_lt (hcp.trans hq)))
            (ev_apply_ne (ne_of_lt hq)),
          oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt hq))]
      · intro _
        rw [hcol, matOf_mul_mulVec, matOf_ωpow, matOf_X]
        apply eq_ev_of_hasNum (hasNum_ω (hasNum_X hw hcp.ne) p _)
        intro a
        by_cases hap : a = p
        · rw [hap, Function.update_self, Function.update_self, if_pos rfl]
          exact ωz_pow_sub_uexp_mul hc1
        · rw [Function.update_of_ne hap, Function.update_of_ne hap, if_neg hap]
          by_cases hac : a = c
          · rw [hac, Function.update_self]; exact hc0 p hcp.ne'
          · rw [Function.update_of_ne hac]; exact hc0 a hac
      · intro h; omega
    · have hcne' : w p ≠ 0 := hcp ▸ hcne
      have hc0' : ∀ a, a ≠ p → w a = 0 := hcp ▸ hc0
      have hc1' : nrm0 (w p) = 1 := hcp ▸ hc1
      rw [sylCol_unit_eq hw hcne' hc0'] at hcol ⊢
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        rw [hcol, hp.2 q hq, matOf_ωpow, oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt hq))]
      · intro _
        rw [hcol, matOf_ωpow]
        apply eq_ev_of_hasNum (hasNum_ω hw _ _)
        intro a
        by_cases hap : a = p
        · rw [hap, Function.update_self, if_pos rfl]
          exact ωz_pow_sub_uexp_mul hc1'
        · rw [Function.update_of_ne hap, if_neg hap]; exact hc0' a hap
      · intro h; omega
  · -- `k > 0`: Lemma 12 on the first two odd entries (Lemma 13)
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
      rw [this] at h3; exact not_isOdd_zero h3
    have hjl := hf.1
    rw [sylCol_H hw hk rfl hf] at hcol ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      rw [hcol, hp.2 q hq, matOf_mul_mulVec, matOf_ωpow, matOf_H,
        oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt ((hjl.trans_le hlp).trans hq))),
        twoLevel_mulVec_of_zero hjl.ne _ (ev_apply_ne (ne_of_lt ((hjl.trans_le hlp).trans hq)))
          (ev_apply_ne (ne_of_lt (lt_of_le_of_lt hlp hq)))]
    · intro h; omega
    · intro _
      rw [hcol, matOf_mul_mulVec, matOf_ωpow, matOf_H]
      obtain ⟨⟨d1, hd1⟩, ⟨d2, hd2⟩⟩ := lemma12 hf.2.1 hf.2.2.1
      have h0 := hasNum_ω hw j (zexp (w j) (w l))
      have e1 : Function.update w j (ωz ^ zexp (w j) (w l) * w j) j +
          Function.update w j (ωz ^ zexp (w j) (w l) * w j) l = δz ^ 3 * d1 := by
        rw [Function.update_self, Function.update_of_ne hjl.ne']; exact hd1
      have e2 : Function.update w j (ωz ^ zexp (w j) (w l) * w j) j -
          Function.update w j (ωz ^ zexp (w j) (w l) * w j) l = δz ^ 3 * d2 := by
        rw [Function.update_self, Function.update_of_ne hjl.ne']; exact hd2
      have h3 := hasNum_H_red h0 hjl.ne e1 e2
      rw [Function.update_idem] at h3
      apply prof_lt_of hw rfl hk h3
      have hsub : oddSet (Function.update (Function.update w j (ηz * δz * d1)) l (ηz * δz * d2)) =
          ((oddSet w).erase l).erase j := by
        ext a
        simp only [mem_oddSet, Finset.mem_erase, Function.update_apply]
        by_cases hal : a = l
        · rw [if_pos hal]; exact iff_of_false (not_isOdd_ηz_δz_mul _) (fun h => h.2.1 hal)
        · by_cases haj : a = j
          · rw [if_neg hal, if_pos haj]
            exact iff_of_false (not_isOdd_ηz_δz_mul _) (fun h => h.1 haj)
          · rw [if_neg hal, if_neg haj]; exact ⟨fun h => ⟨haj, hal, h⟩, fun h => h.2.2⟩
      rw [hsub, Finset.card_erase_of_mem, Finset.card_erase_of_mem (mem_oddSet.2 hf.2.2.1)]
      · omega
      · exact Finset.mem_erase.2 ⟨hjl.ne, mem_oddSet.2 hf.2.1⟩

/-- Theorem 18: the syllable of a state `s ≠ I` lowers its level. -/
theorem level_syl_lt {s : St n} (hs : s ≠ 1) :
    level (FreeMonoid.lift (sem n) (syl s) * s) < level s := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  obtain ⟨h1, h2, h3⟩ := syl_cols hp
  apply level_lt_of_cols hp h1
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · exact Or.inl (h2 hk)
  · exact Or.inr (h3 hk)

/-- The relation "smaller level" on states is well founded. -/
theorem wf_level : WellFounded (fun s t : St n => level s < level t) :=
  InvImage.wf level wellFounded_lt

open Classical in
/-- The normal word of a state (Definition 25, Remark 26): its syllables down
to `I`, the last one first, so that `⟦nw s⟧ s = I`. -/
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

/-- Theorem 18: the normal word reduces its state to the identity. -/
theorem nw_reduces (s : St n) : FreeMonoid.lift (sem n) (nw s) * s = 1 := by
  induction s using wf_level.induction with
  | _ s ih =>
    by_cases h : s = 1
    · subst h; rw [nw_one, map_one, one_mul]
    · rw [nw_of_ne h, map_mul, mul_assoc]
      exact ih _ (level_syl_lt h)

end

end QCert.Greylyn
