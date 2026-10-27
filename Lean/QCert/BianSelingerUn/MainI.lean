/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the Main Lemma for `G = i_[0]` (Case 1)

Case 1 of the proof of Lemma 3.7 (Appendix A), with `j` the first odd
entry of the numerator `w` of the pivot column of `s`:

* 1.1 `j > 0`: disjoint, `r = i_[0] s` has the syllable of `s`;
* 1.2 `j = 0`, `k = 0`, `p = 0`: `N' i_[0] = N` (or `r = I`);
* 1.3 `j = 0`, `k = 0`, `p > 0`: `N' i_[0] ∼ N` by (1);
* 1.4 `j = 0`, `k > 0`: by (17) when `q = 0` and by (21) when `q = 1`.

The general facts about pivot columns used by all cases come first.
-/
import QCert.BianSelingerUn.Square

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-! ### Pivot columns -/

/-- Corollary 2.8: at exponent `0` the pivot column is a unit `u e_c`, `c ≤ p`. -/
theorem unit_col {s : St n} {p : Fin n} (hp : IsPivot s p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) 0 w) :
    ∃ c, (w c).norm = 1 ∧ (∀ a, a ≠ c → w a = 0) ∧ c ≤ p := by
  have hsum := sum_norm_eq (col_unit s p) hw
  rw [pow_zero] at hsum
  obtain ⟨c, hc1, hc0⟩ := unit_of_sum_norm_one hsum
  refine ⟨c, hc1, hc0, ?_⟩
  by_contra h
  have := hasNum_zero_of_entry hp hw (not_le.1 h)
  rw [this] at hc1; simp at hc1

theorem ne_zero_of_norm {g : GaussianInt} (h : g.norm = 1) : g ≠ 0 := by
  rintro rfl; simp at h

/-- Lemma 2.9 and the choice of Algorithm 2.14 at a positive exponent. -/
theorem pos_col {s : St n} {p : Fin n} (hp : IsPivot s p) {k : ℕ} {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) k w) (hk : 0 < k) (hl : lde (col s p) = k) :
    ∃ j l, FirstTwo w j l ∧ l ≤ p := by
  subst hl
  have hev := even_card_odd (col_unit s p) hw hk
  obtain ⟨j0, hj0⟩ := exists_odd hw hk
  have h2 : 2 ≤ (oddSet w).card := by
    have : 0 < (oddSet w).card := Finset.card_pos.2 ⟨j0, mem_oddSet.2 hj0⟩
    have hev' : Even (oddSet w).card := hev
    obtain ⟨r, hr⟩ := hev'
    omega
  obtain ⟨j, l, hf⟩ := exists_firstTwo h2
  refine ⟨j, l, hf, ?_⟩
  by_contra h
  have := hasNum_zero_of_entry hp hw (not_le.1 h)
  have h3 := hf.2.2.1
  rw [this] at h3; exact absurd h3 (by decide)

/-- A state below `s` agrees with the identity beyond the pivot of `s`. -/
theorem cols_of_level_le {s t : St n} {p : Fin n} (hs : IsPivot s p) (h : level t ≤ level s) :
    ∀ q, p < q → col t q = ev q := by
  intro q hq
  by_cases ht : t = 1
  · subst ht; exact col_one q
  obtain ⟨p', hp'⟩ := exists_pivot ht
  rw [level_eq hp', level_eq hs, Prod.Lex.toLex_le_toLex] at h
  have : (p' : ℕ) ≤ p := by
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  exact hp'.2 q (Fin.lt_def.2 (by have : (p : ℕ) < q := hq; omega))

theorem allBelow_mon' {s : St n} {p : Fin n} (hs : IsPivot s p) (hs1 : s ≠ 1) {w : Word (Gen n)}
    (hw : ∀ x ∈ FreeMonoid.toList w, MonLetter p x)
    (hk : 0 < lde (col s p) ∨ ∀ x ∈ FreeMonoid.toList w, ¬ Touches p x) :
    AllBelow (level s) (⟪syl s⟫ * s) w :=
  allBelow_mon hs (level_syl_lt hs1) (cols_of_level_le hs (level_syl_lt hs1).le) hw hk

theorem expo_iz_mul {u : GaussianInt} (hu : u.norm = 1) : (expo (iz * u) + 1) % 4 = expo u := by
  rcases eq_of_norm_eq_one hu with rfl | rfl | rfl | rfl <;> decide

theorem norm_iz_mul {u : GaussianInt} (hu : u.norm = 1) : (iz * u).norm = 1 := by
  rcases eq_of_norm_eq_one hu with rfl | rfl | rfl | rfl <;> decide

theorem qexp_iz_mul {a b : GaussianInt} (ha : GOdd a) :
    qexp (iz * a) b = 1 - qexp a b := by
  unfold GOdd at ha
  simp only [qexp, iz_mul]
  split_ifs <;> omega

theorem gi_pow_succ_mod (a : Fin n) (e e' : ℕ) (h : (e' + 1) % 4 = e) :
    gi a ^ e' * gi a = gi a ^ e := by
  rw [← pow_succ, gi_pow_mod, h]

theorem cl_syl_unit_lt {c p : Fin n} (h : c < p) (e : ℕ) :
    cl (X c p h * i c ^ e) = gX c p h * gi c ^ e := by
  rw [map_mul, map_pow, cl_X, cl_i]

/-! ### Case 1: `G = i_[0]` -/

theorem main_i {s : St n} (hs : s ≠ 1) (a : Fin n) (ha : (a : ℕ) = 0)
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.i a) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  have hap : a ≤ p := Fin.le_def.2 (by omega)
  have hxa : ext (Gen.i a) ≤ (p : ℕ) := by show (a : ℕ) ≤ p; omega
  obtain ⟨w, hw⟩ := lde_spec (hasNum_exists s p)
  have hw' := hasNum_sem_i hw a
  rcases Nat.eq_zero_or_pos (lde (col s p)) with h0 | hpos
  · ---- `k = 0`
    rw [h0] at hw hw'
    obtain ⟨c, hc1, hc0, hcp⟩ := unit_col hp hw
    have hcne := ne_zero_of_norm hc1
    by_cases hca : c = a
    · rw [hca] at hc1 hc0 hcp hcne
      have hz' : ∀ x, x ≠ a → Function.update w a (iz * w a) x = 0 := by
        intro x hx; rw [Function.update_of_ne hx]; exact hc0 x hx
      have hne' : Function.update w a (iz * w a) a ≠ 0 := by
        rw [Function.update_self]; exact ne_zero_of_norm (norm_iz_mul hc1)
      by_cases hpa : p = a
      · ---- Case 1.2: `j = 0`, `k = 0`, `p = 0`
        rw [hpa] at hp hw hw' hxa
        have hsyl : syl s = i a ^ expo (w a) := by rw [syl_eq hp, sylCol_unit_eq hw hcne hc0]
        by_cases h1 : iz * w a = 1
        · -- `r = I`
          have hr1 : sem n (Gen.i a) * s = 1 := by
            rw [eq_one_iff]
            intro q
            rcases eq_or_ne q a with hqa | hqa
            · rw [hqa]
              apply eq_ev_of_hasNum hw'
              intro x
              by_cases hx : x = a
              · rw [hx, Function.update_self, h1, if_pos rfl]
              · rw [if_neg hx]; exact hz' x hx
            · have : a < q := lt_of_le_of_ne (Fin.le_def.2 (by omega)) (Ne.symm hqa)
              rw [col_sem, hp.2 q this, mat_mulVec_ev_of_lt _ (by show (a : ℕ) < q; exact this)]
          have he : expo (w a) = 1 := by
            have : w a = -iz := by
              have h2 : iz * (iz * w a) = iz := by rw [h1, mul_one]
              rw [← mul_assoc] at h2
              have h3 : iz * iz = -1 := by decide
              rw [h3, neg_one_mul] at h2
              rw [← neg_neg (w a), h2]
            rw [this]; decide
          unfold Step
          rw [hr1, nw_one, one_mul, nw_of_ne hs, hsyl, he, pow_one, FreeMonoid.lift_eval_of, hr1,
            nw_one, one_mul]
        · -- `r ≠ I`: `N' i_[0] = N`
          have hrp : IsPivot (sem n (Gen.i a) * s) a := by
            refine isPivot_sem hp hxa (fun heq => h1 ?_)
            rw [← col_sem] at heq
            have := hw' a
            rw [heq, Function.update_self, pow_zero, one_mul] at this
            simp only [ev] at this
            exact GaussianInt.toComplex_inj.1 (this.symm.trans GaussianInt.toComplex_one.symm)
          have hsylr : syl (sem n (Gen.i a) * s) = i a ^ expo (iz * w a) := by
            rw [syl_eq hrp, sylCol_unit_eq hw' hne' hz', Function.update_self]
          refine step_sq hs hrp.ne_one 1 ?_ (allBelow_one (level_syl_lt hs)) hstep
          rw [hsylr, hsyl, one_mul]
          simp only [map_pow, cl_i]
          exact gi_pow_succ_mod a _ _ (expo_iz_mul hc1)
      · ---- Case 1.3: `j = 0`, `k = 0`, `p > 0`
        have hlt : a < p := lt_of_le_of_ne hap (Ne.symm hpa)
        have hsyl : syl s = X a p hlt * i a ^ expo (w a) := by
          rw [syl_eq hp, sylCol_unit_lt hw hcne hc0 hlt]
        have hrp : IsPivot (sem n (Gen.i a) * s) p := by
          refine isPivot_sem hp hxa (fun heq => hne' ?_)
          rw [← col_sem] at heq
          have := hw' a
          rw [heq, pow_zero, one_mul] at this
          simp only [ev, if_neg (Ne.symm hpa)] at this
          exact (GaussianInt.toComplex_eq_zero.1 this.symm)
        have hsylr : syl (sem n (Gen.i a) * s) = X a p hlt * i a ^ expo (iz * w a) := by
          rw [syl_eq hrp, sylCol_unit_lt hw' hne' hz' hlt, Function.update_self]
        refine step_sq hs hrp.ne_one 1 ?_ (allBelow_one (level_syl_lt hs)) hstep
        rw [hsylr, hsyl, one_mul]
        simp only [map_mul, map_pow, cl_X, cl_i]
        rw [mul_assoc, gi_pow_succ_mod a _ _ (expo_iz_mul hc1)]
    · ---- Case 1.1 at `k = 0`: disjoint
      have hwa : w a = 0 := hc0 a (Ne.symm hca)
      have hw'' : HasNum (col (sem n (Gen.i a) * s) p) 0 w := by
        rw [hwa, mul_zero, ← hwa, Function.update_eq_self] at hw'; exact hw'
      have hcol : col (sem n (Gen.i a) * s) p = col s p := hw''.eq_of hw
      have hrp : IsPivot (sem n (Gen.i a) * s) p :=
        isPivot_sem hp hxa (by rw [← col_sem, hcol]; exact hp.1)
      have hap' : a ≠ p := by
        intro e; rw [← e] at hcp
        exact hca (Fin.ext (by have := Fin.le_def.1 hcp; omega))
      refine step_disj hs hrp.ne_one (by rw [syl_eq hrp, syl_eq hp, hcol])
        (by rw [level_eq hrp, level_eq hp, hcol]) ?_ hstep
      rw [syl_eq hp, map_mul, map_mul]
      rcases lt_or_eq_of_le hcp with hlt | hcp'
      · rw [sylCol_unit_lt hw hcne hc0 hlt]
        simp only [map_mul, map_pow, cl_X, cl_i]
        have h1 : Commute (gi a) (gX c p hlt) := e5 a c p hlt (Ne.symm hca) hap'
        have h2 : Commute (gi a) (gi c) := e4 a c (Ne.symm hca)
        exact ((h1.mul_right (h2.pow_right _)).eq).symm
      · rw [hcp'] at hcne hc0 hca
        rw [sylCol_unit_eq hw hcne hc0]
        simp only [map_pow, cl_i]
        exact ((Commute.pow_right (e4 a p (Ne.symm hca)) _).eq).symm
  · ---- `k > 0`
    obtain ⟨j, l, hf, hlp⟩ := pos_col hp hw hpos rfl
    obtain ⟨hjl, hj, hl, hbefore, hbetween⟩ := hf
    have hjl' : j < l := hjl
    by_cases hja : j = a
    · ---- Case 1.4: `j = 0`, `k > 0`
      rw [hja] at hjl hj hbefore hbetween hjl'
      have hf' : FirstTwo (Function.update w a (iz * w a)) a l := by
        refine ⟨hjl, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_self, GOdd_iz_mul]; exact hj
        · rw [Function.update_of_ne hjl.ne']; exact hl
        · intro x hx; exact absurd hx (by have := Fin.lt_def.1 hx; omega)
        · intro x hx hx'; rw [Function.update_of_ne hx.ne']; exact hbetween x hx hx'
      have hodd' : GOdd (Function.update w a (iz * w a) a) := hf'.2.1
      have hrp : IsPivot (sem n (Gen.i a) * s) p := by
        refine isPivot_sem hp hxa ?_
        rw [← col_sem]; exact ne_ev_of_odd hw' hpos ⟨a, hodd'⟩ p
      have hsyl : syl s = K a l hjl ^ 7 * i l ^ qexp (w a) (w l) := by
        rw [syl_eq hp]; exact sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩
      have hsylr : syl (sem n (Gen.i a) * s) = K a l hjl ^ 7 * i l ^ (1 - qexp (w a) (w l)) := by
        rw [syl_eq hrp, sylCol_K hw' hpos (lde_of_odd hw' a hodd') hf', K_congr hf'.1 hjl rfl rfl,
          Function.update_self, Function.update_of_ne hjl.ne', qexp_iz_mul hj]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (qexp_le (w a) (w l)) with hq | hq
      · -- `q = 0`: by (17), `G' = i_[0] i_[ℓ]`
        refine step_sq hs hrp.ne_one (i a * i l) ?_ (allBelow_mon' hp hs ?_ (Or.inl hpos)) hstep
        · rw [hsylr, hsyl, hq]
          simp only [map_mul, map_pow, cl_K, cl_i, cl_ofi, pow_zero, pow_one, mul_one,
            Nat.sub_zero]
          simp only [mul_assoc]
          simpa only [mul_one] using f17 a l hjl 1
        · intro x hx
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
            List.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hap
          · exact hlp
      · -- `q = 1`: by (21), `G' = i_[0] i_[ℓ] X_[0,ℓ]`
        refine step_sq hs hrp.ne_one (i a * i l * X a l hjl) ?_
          (allBelow_mon' hp hs ?_ (Or.inl hpos)) hstep
        · rw [hsylr, hsyl, hq]
          simp only [map_mul, map_pow, cl_X, cl_K, cl_i, cl_ofi, pow_zero, pow_one, mul_one,
            Nat.sub_self]
          simp only [mul_assoc]
          simpa only [mul_one] using f21 a l hjl 1
        · intro x hx
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
            List.mem_singleton] at hx
          rcases hx with (rfl | rfl) | rfl
          · exact hap
          · exact hlp
          · exact hlp
    · ---- Case 1.1 at `k > 0`: disjoint
      have haj : a < j := lt_of_le_of_ne (Fin.le_def.2 (by omega)) (Ne.symm hja)
      have hwa : ¬ GOdd (w a) := hbefore a haj
      have hal : a ≠ l := (haj.trans hjl).ne
      have hf' : FirstTwo (Function.update w a (iz * w a)) j l := by
        refine ⟨hjl, ?_, ?_, ?_, ?_⟩
        · rw [Function.update_of_ne hja]; exact hj
        · rw [Function.update_of_ne hal.symm]; exact hl
        · intro x hx
          by_cases hxa : x = a
          · subst hxa; rw [Function.update_self, GOdd_iz_mul]; exact hwa
          · rw [Function.update_of_ne hxa]; exact hbefore x hx
        · intro x hx hx'
          rw [Function.update_of_ne (haj.trans hx).ne']; exact hbetween x hx hx'
      have hrp : IsPivot (sem n (Gen.i a) * s) p := by
        refine isPivot_sem hp hxa ?_
        rw [← col_sem]; exact ne_ev_of_odd hw' hpos ⟨j, hf'.2.1⟩ p
      have hsyl : syl s = K j l hjl ^ 7 * i l ^ qexp (w j) (w l) := by
        rw [syl_eq hp]; exact sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩
      have hsylr : syl (sem n (Gen.i a) * s) = syl s := by
        rw [hsyl, syl_eq hrp, sylCol_K hw' hpos (lde_of_odd hw' j hf'.2.1) hf',
          K_congr hf'.1 hjl rfl rfl, Function.update_of_ne hja, Function.update_of_ne hal.symm]
      refine step_disj hs hrp.ne_one hsylr
        (by rw [level_eq hrp, level_eq hp, prof_sem_i]) ?_ hstep
      rw [hsyl]
      simp only [map_mul, map_pow, cl_K, cl_i]
      have h1 : Commute (gi a) (gK j l hjl) := e6 a j l hjl haj.ne hal
      have h2 : Commute (gi a) (gi l) := e4 a l hal
      exact (((h1.pow_right 7).mul_right (h2.pow_right _)).eq).symm

end

end QCert.BianSelingerUn
