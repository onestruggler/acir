/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the Main Lemma for `G = K_[0,1]` (Case 2) and the base case

Case 2 of the proof of Lemma 3.7, with `j < ℓ` the first two odd entries of
the numerator `w` of the pivot column (or `c` the index of the unit entry
when `k = 0`):

* 2.1.1 `k = 0`, `c < 2`: retrograde (the normal edge of `r` is `K†_[0,1]`);
* 2.1.2 `k = 0`, `c ≥ 2`: disjoint;
* 2.2.1 `j = 0`, `ℓ = 1`: by (22) when `q = 0` (then `r` is below `s`) and
  by (23) when `q = 1`;
* 2.2.2 `j = 0`, `ℓ > 1` and 2.2.3 `j = 1`: retrograde;
* 2.2.4 `j > 1`: disjoint, or retrograde when the new entries `0, 1` are odd.

When the pivot of `s` is `0` (in particular for `s = I`) the edge is
retrograde as well.  The edges out of `I` along basic generators
(`base_step'`) are retrograde.
-/
import QCert.BianSelingerUn.MainI

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-- The numerator of a basis vector. -/
def ind (c : Fin n) : Fin n → GaussianInt := fun a => if a = c then 1 else 0

theorem hasNum_ev (c : Fin n) : HasNum (ev c) 0 (ind c) := by
  intro a; by_cases ha : a = c <;> simp [ev, ind, ha]

theorem qexp_add_sub (a b : GaussianInt) : qexp (a + b) (a - b) = 0 := by
  unfold qexp; rw [if_pos]; simp only [Zsqrtd.re_add, Zsqrtd.re_sub]; omega

theorem GOdd_one : GOdd (1 : GaussianInt) := by decide
theorem GOdd_neg_one : GOdd (-1 : GaussianInt) := by decide

theorem qexp_one_neg_one : qexp (1 : GaussianInt) (-1) = 0 := by decide

/-! ### Retrograde edges from low states -/

theorem step_K_low {s : St n} {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0) (ho : (o : ℕ) = 1)
    (hlow : ∀ q, z < q → col s q = ev q) : Step s (Gen.K z o hzo) := by
  have hw := hasNum_sem_K (q := o) (by rw [hlow o hzo]; exact hasNum_ev o) hzo
  set w' := Function.update (Function.update (fun c => γz * ind o c) z (ind o z + ind o o)) o
    (ind o z - ind o o) with hw'def
  have hwz : w' z = 1 := by
    rw [hw'def, Function.update_of_ne hzo.ne, Function.update_self]
    simp only [ind, if_neg hzo.ne]; simp
  have hwo : w' o = -1 := by simp [w', ind, hzo.ne]
  have hf : FirstTwo w' z o := by
    refine ⟨hzo, by rw [hwz]; exact GOdd_one, by rw [hwo]; exact GOdd_neg_one, ?_, ?_⟩
    · intro x hx; exact absurd hx (by have := Fin.lt_def.1 hx; omega)
    · intro x hx hx'; exact absurd hx' (by have := Fin.lt_def.1 hx; have := Fin.lt_def.1 hx'; omega)
  have hodd : GOdd (w' z) := hf.2.1
  have hrp : IsPivot (sem n (Gen.K z o hzo) * s) o := by
    refine ⟨ne_ev_of_odd hw (by omega) ⟨z, hodd⟩ o, fun q hq => ?_⟩
    rw [col_sem, hlow q (hzo.trans hq), mat_mulVec_ev_of_lt _ (by show (o : ℕ) < q; exact hq)]
  refine step_retro' hrp.ne_one (u := K z o hzo ^ 7 * i o ^ 0) ?_ ?_
  · rw [syl_eq hrp, sylCol_K hw (by omega) (lde_of_odd hw z hodd) hf, K_congr hf.1 hzo rfl rfl,
      hwz, hwo, qexp_one_neg_one]
  · simp only [map_mul, map_pow, cl_K, cl_ofK, cl_i, pow_zero, mul_one]
    exact gK_pow_seven_mul z o hzo

theorem GOdd_unit {g : GaussianInt} (h : g.norm = 1) : GOdd g := by
  have := norm_emod_two g
  rw [h] at this
  unfold GOdd; omega

/-- `X_[α,α+1]` from a state that is the identity beyond `α` is retrograde. -/
theorem step_X_low {s : St n} {a b : Fin n} (hab : a < b)
    (hlow : ∀ q, a < q → col s q = ev q) : Step s (Gen.X a b hab) := by
  have hw := hasNum_sem_X (q := b) (by rw [hlow b hab]; exact hasNum_ev b) hab
  have hval : Function.update (Function.update (ind b) a (ind b b)) b (ind b a) = ind a := by
    funext x
    by_cases hxb : x = b
    · subst hxb; simp [ind, hab.ne, hab.ne']
    · by_cases hxa : x = a
      · subst hxa; simp [ind, hab.ne, hab.ne']
      · simp [ind, hxb, hxa]
  rw [hval] at hw
  have hcol : col (sem n (Gen.X a b hab) * s) b = ev a := hw.eq_of (hasNum_ev a)
  have hrp : IsPivot (sem n (Gen.X a b hab) * s) b := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [hcol]; intro h
      have := congrFun h a
      simp [ev, hab.ne] at this
    · rw [col_sem, hlow q (hab.trans hq), mat_mulVec_ev_of_lt _ (by show (b : ℕ) < q; exact hq)]
  refine step_retro' hrp.ne_one (u := X a b hab * i a ^ 0) ?_ ?_
  · rw [syl_eq hrp, sylCol_unit_lt hw (by simp [ind]) (fun x hx => by simp [ind, hx]) hab]
    simp [ind]; rfl
  · simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i, pow_zero, mul_one]
    exact e2 a b hab

/-- `i_[0]` from `I` is retrograde. -/
theorem step_i_base (a : Fin n) : Step (1 : St n) (Gen.i a) := by
  have hw := hasNum_sem_i (q := a) (by rw [col_one]; exact hasNum_ev a) a
  have hval : Function.update (ind a) a (iz * ind a a) = fun x => if x = a then iz else 0 := by
    funext x; by_cases hx : x = a
    · subst hx; simp [ind]
    · simp [ind, hx]
  rw [hval] at hw
  have hrp : IsPivot (sem n (Gen.i a) * 1) a := by
    refine ⟨fun h => ?_, fun q hq => ?_⟩
    · have := hw a
      rw [h] at this; simp [ev, toComplex_iz] at this
      have h2 := congrArg Complex.im this; simp at h2
    · rw [col_sem, col_one, mat_mulVec_ev_of_lt _ (by show (a : ℕ) < q; exact hq)]
  refine step_retro' hrp.ne_one (u := i a ^ 3) ?_ ?_
  · rw [syl_eq hrp, sylCol_unit_eq hw (by simp; decide) (fun x hx => by simp [hx])]
    simp; rfl
  · simp only [map_mul, map_pow, cl_i, cl_ofi]
    exact gi_pow_three_mul a

/-- The edges out of `I` (base case of Lemma 3.6). -/
theorem base_step' (x : Gen n) (hx : Basic x) : Step (1 : St n) x := by
  cases x with
  | X a b hab => exact step_X_low hab (fun q _ => col_one q)
  | K a b hab => exact step_K_low hab hx.1 hx.2 (fun q _ => col_one q)
  | i a => exact step_i_base a

/-- Halving the sum and difference of two odd numbers with `q = 1`. -/
theorem half_odd {a b : GaussianInt} (ha : GOdd a) (hb : GOdd b) (hq : qexp a b = 1) :
    ∃ d d', a + b = γz * d ∧ a - b = γz * d' ∧ GOdd d ∧ GOdd d' ∧ qexp d d' = 1 := by
  unfold GOdd at ha hb
  unfold qexp at hq
  by_cases h : a.re % 2 = b.re % 2
  · simp [h] at hq
  refine ⟨⟨((a + b).re + (a + b).im) / 2, ((a + b).im - (a + b).re) / 2⟩,
    ⟨((a - b).re + (a - b).im) / 2, ((a - b).im - (a - b).re) / 2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [γz_mul]; ext <;> simp <;> omega
  · rw [γz_mul]; ext <;> simp <;> omega
  · unfold GOdd; simp; omega
  · unfold GOdd; simp; omega
  · unfold qexp; simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub]
    rw [if_neg]; omega

theorem even_split {g : GaussianInt} (h : ¬ GOdd g) : ∃ c, g = γz * c := (not_GOdd_iff g).1 h

/-! ### Case 2: `G = K_[0,1]` -/

theorem main_K {s : St n} (hs : s ≠ 1) {z o : Fin n} (hzo : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1)
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.K z o hzo) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  by_cases hp0 : (p : ℕ) = 0
  · exact step_K_low hzo hz ho (fun q hq => hp.2 q (Fin.lt_def.2 (by
      have := Fin.lt_def.1 hq; omega)))
  have hop : o ≤ p := Fin.le_def.2 (by omega)
  have hxK : ext (Gen.K z o hzo) ≤ (p : ℕ) := by show (o : ℕ) ≤ p; omega
  obtain ⟨w, hw⟩ := lde_spec (hasNum_exists s p)
  have hwK := hasNum_sem_K hw hzo
  have hzval : ∀ x : Fin n, x = z ↔ (x : ℕ) = 0 := fun x => by
    constructor
    · rintro rfl; exact hz
    · intro hx; exact Fin.ext (by omega)
  have hoval : ∀ x : Fin n, x = o ↔ (x : ℕ) = 1 := fun x => by
    constructor
    · rintro rfl; exact ho
    · intro hx; exact Fin.ext (by omega)
  have wKz : Function.update (Function.update (fun c => γz * w c) z (w z + w o)) o
      (w z - w o) z = w z + w o := by
    rw [Function.update_of_ne hzo.ne, Function.update_self]
  have wKo : Function.update (Function.update (fun c => γz * w c) z (w z + w o)) o
      (w z - w o) o = w z - w o := by
    rw [Function.update_self]
  -- retrograde when `w z ± w o` are the new first two odd entries at exponent `k + 1`
  have retro : GOdd (w z + w o) → GOdd (w z - w o) → Step s (Gen.K z o hzo) := by
    intro h1 h2
    have hf : FirstTwo (Function.update (Function.update (fun c => γz * w c) z (w z + w o)) o
        (w z - w o)) z o := by
      refine ⟨hzo, by rw [wKz]; exact h1, by rw [wKo]; exact h2, ?_, ?_⟩
      · intro x hx; exact absurd hx (by have := Fin.lt_def.1 hx; omega)
      · intro x hx hx'
        exact absurd hx' (by have := Fin.lt_def.1 hx; have := Fin.lt_def.1 hx'; omega)
    have hrp : IsPivot (sem n (Gen.K z o hzo) * s) p :=
      isPivot_sem hp hxK (by rw [← col_sem]; exact ne_ev_of_odd hwK (by omega) ⟨z, hf.2.1⟩ p)
    refine step_retro' hrp.ne_one (u := K z o hzo ^ 7 * i o ^ 0) ?_ ?_
    · rw [syl_eq hrp, sylCol_K hwK (by omega) (lde_of_odd hwK z hf.2.1) hf, K_congr hf.1 hzo rfl rfl,
        wKz, wKo, qexp_add_sub]
    · simp only [map_mul, map_pow, cl_K, cl_ofK, cl_i, pow_zero, mul_one]
      exact gK_pow_seven_mul z o hzo
  rcases Nat.eq_zero_or_pos (lde (col s p)) with h0 | hpos
  · ---- `k = 0`
    rw [h0] at hw hwK
    obtain ⟨c, hc1, hc0, hcp⟩ := unit_col hp hw
    have hcne := ne_zero_of_norm hc1
    by_cases hc2 : (c : ℕ) < 2
    · ---- Case 2.1.1: retrograde
      rcases (show (c : ℕ) = 0 ∨ (c : ℕ) = 1 by omega) with hc | hc
      · have hcz : c = z := (hzval c).2 hc
        rw [hcz] at hc1 hc0
        have hwo : w o = 0 := hc0 o hzo.ne'
        apply retro
        · rw [hwo, add_zero]; exact GOdd_unit hc1
        · rw [hwo, sub_zero]; exact GOdd_unit hc1
      · have hco : c = o := (hoval c).2 hc
        rw [hco] at hc1 hc0
        have hwz : w z = 0 := hc0 z hzo.ne
        apply retro
        · rw [hwz, zero_add]; exact GOdd_unit hc1
        · rw [hwz, zero_sub, GOdd_neg]; exact GOdd_unit hc1
    · ---- Case 2.1.2: disjoint
      have hcz : c ≠ z := fun e => hc2 (by rw [e, hz]; omega)
      have hco : c ≠ o := fun e => hc2 (by rw [e, ho]; omega)
      have hwz : w z = 0 := hc0 z (Ne.symm hcz)
      have hwo : w o = 0 := hc0 o (Ne.symm hco)
      have hwK' : HasNum (col (sem n (Gen.K z o hzo) * s) p) (0 + 1) (fun x => γz * w x) := by
        have e : Function.update (Function.update (fun c => γz * w c) z (w z + w o)) o
            (w z - w o) = fun x => γz * w x := by
          funext x
          rw [Function.update_apply, Function.update_apply]
          split_ifs with h1 h2
          · rw [h1, hwz, hwo]; simp
          · rw [h2, hwz, hwo]; simp
          · rfl
        rw [← e]; exact hwK
      have hcol : col (sem n (Gen.K z o hzo) * s) p = col s p :=
        (hwK'.pred w (fun _ => rfl)).eq_of hw
      have hrp : IsPivot (sem n (Gen.K z o hzo) * s) p :=
        isPivot_sem hp hxK (by rw [← col_sem, hcol]; exact hp.1)
      refine step_disj hs hrp.ne_one (by rw [syl_eq hrp, syl_eq hp, hcol])
        (by rw [level_eq hrp, level_eq hp, hcol]) ?_ hstep
      have hc2' : 2 ≤ (c : ℕ) := by omega
      have hpz : p ≠ z := fun e => hp0 (by rw [e, hz])
      have hpo : p ≠ o := fun e => by
        have := Fin.le_def.1 hcp; rw [e, ho] at this; omega
      rw [syl_eq hp]
      rcases lt_or_eq_of_le hcp with hlt | hcp'
      · rw [sylCol_unit_lt hw hcne hc0 hlt]
        simp only [map_mul, map_pow, cl_X, cl_i, cl_ofK]
        have h1 : Commute (gX c p hlt) (gK z o hzo) := e8 c p z o hlt hzo hcz hco hpz hpo
        have h2 : Commute (gi c) (gK z o hzo) := e6 c z o hzo hcz hco
        exact (h1.mul_left (h2.pow_left _)).eq
      · rw [hcp'] at hcne hc0
        rw [sylCol_unit_eq hw hcne hc0]
        simp only [map_mul, map_pow, cl_i, cl_ofK]
        exact (Commute.pow_left (e6 p z o hzo hpz hpo) _).eq
  · ---- `k > 0`
    obtain ⟨j, l, hf, hlp⟩ := pos_col hp hw hpos rfl
    obtain ⟨hjl, hj, hl, hbefore, hbetween⟩ := hf
    by_cases h221 : j = z ∧ l = o
    · ---- Case 2.2.1
      obtain ⟨hjz, hlo⟩ := h221
      have hfzo : FirstTwo w z o := by
        rw [← hjz, ← hlo]; exact ⟨hjl, hj, hl, hbefore, hbetween⟩
      have hzodd := hfzo.2.1
      have hoodd := hfzo.2.2.1
      have hsyl : syl s = K z o hzo ^ 7 * i o ^ qexp (w z) (w o) := by
        rw [syl_eq hp, sylCol_K hw hpos rfl hfzo]
      have hzp : z ≤ p := (hzo.trans_le hop).le
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (qexp_le (w z) (w o)) with hq | hq
      · -- `q = 0`: by (22), `r` is below `s`
        refine step_sq0 hs (i z * i z * i z * i o * i o * i o) ?_
          (allBelow_mon' hp hs ?_ (Or.inl hpos)) hstep
        · rw [hsyl, hq]
          simp only [map_mul, map_pow, cl_K, cl_ofK, cl_i, pow_zero, mul_one]
          simp only [mul_assoc]
          simpa only [mul_one] using f22 z o hzo 1
        · intro x hx
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
            List.mem_singleton] at hx
          rcases hx with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
          all_goals first | exact hzp | exact hop
      · -- `q = 1`: by (23)
        obtain ⟨d, d', hd, hd', hdo, hdo', hdq⟩ := half_odd hzodd hoodd hq
        have hw2 : HasNum (col (sem n (Gen.K z o hzo) * s) p) (lde (col s p))
            (Function.update (Function.update w z d) o d') := by
          apply hwK.pred
          intro x
          rw [Function.update_apply, Function.update_apply, Function.update_apply,
            Function.update_apply]
          split_ifs <;> first | rfl | exact hd' | exact hd
        have hf2 : FirstTwo (Function.update (Function.update w z d) o d') z o := by
          refine ⟨hzo, ?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne hzo.ne, Function.update_self]; exact hdo
          · rw [Function.update_self]; exact hdo'
          · intro x hx; exact absurd hx (by have := Fin.lt_def.1 hx; omega)
          · intro x hx hx'
            exact absurd hx' (by have := Fin.lt_def.1 hx; have := Fin.lt_def.1 hx'; omega)
        have hrp : IsPivot (sem n (Gen.K z o hzo) * s) p :=
          isPivot_sem hp hxK (by rw [← col_sem]; exact ne_ev_of_odd hw2 hpos ⟨z, hf2.2.1⟩ p)
        have hsylr : syl (sem n (Gen.K z o hzo) * s) = K z o hzo ^ 7 * i o ^ 1 := by
          rw [syl_eq hrp, sylCol_K hw2 hpos (lde_of_odd hw2 z hf2.2.1) hf2,
            K_congr hf2.1 hzo rfl rfl, Function.update_of_ne hzo.ne, Function.update_self,
            Function.update_self, hdq]
        refine step_sq hs hrp.ne_one (i o * i o * i o * X z o hzo) ?_
          (allBelow_mon' hp hs ?_ (Or.inl hpos)) hstep
        · rw [hsylr, hsyl, hq]
          simp only [map_mul, map_pow, cl_X, cl_K, cl_ofK, cl_i, pow_one]
          simp only [mul_assoc]
          simpa only [mul_one] using f23 z o hzo 1
        · intro x hx
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
            List.mem_singleton] at hx
          rcases hx with ((rfl | rfl) | rfl) | rfl
          all_goals exact hop
    by_cases h223 : j = z ∨ j = o
    · ---- Cases 2.2.2 and 2.2.3: retrograde
      have hodd : ¬ (GOdd (w z) ↔ GOdd (w o)) := by
        rcases h223 with hjz | hjo
        · rw [hjz] at hj hjl
          have hlo : l ≠ o := fun e => h221 ⟨hjz, e⟩
          have hwo : ¬ GOdd (w o) := hbetween o (by rw [hjz]; exact hzo)
            (lt_of_le_of_ne (Fin.le_def.2 (by have := Fin.lt_def.1 hjl; omega)) (Ne.symm hlo))
          tauto
        · rw [hjo] at hj hbefore
          have hwz : ¬ GOdd (w z) := hbefore z hzo
          tauto
      exact retro ((GOdd_add _ _).2 hodd) ((GOdd_sub _ _).2 hodd)
    · ---- Case 2.2.4
      push Not at h223
      obtain ⟨hjz, hjo⟩ := h223
      have hzj : z < j := Fin.lt_def.2 (by have := (hzval j).not.1 hjz; omega)
      have hoj : o < j := Fin.lt_def.2 (by
        have h1 := (hzval j).not.1 hjz; have h2 := (hoval j).not.1 hjo; omega)
      obtain ⟨a0, ha0⟩ := even_split (hbefore z hzj)
      obtain ⟨a1, ha1⟩ := even_split (hbefore o hoj)
      have hw2 : HasNum (col (sem n (Gen.K z o hzo) * s) p) (lde (col s p))
          (Function.update (Function.update w z (a0 + a1)) o (a0 - a1)) := by
        apply hwK.pred
        intro x
        rw [Function.update_apply, Function.update_apply, Function.update_apply,
          Function.update_apply]
        split_ifs <;> first | rfl | (rw [ha0, ha1]; ring)
      have hlz : l ≠ z := (hzj.trans hjl).ne'
      have hlo : l ≠ o := (hoj.trans hjl).ne'
      have hw2j : Function.update (Function.update w z (a0 + a1)) o (a0 - a1) j = w j := by
        rw [Function.update_of_ne hjo, Function.update_of_ne hjz]
      have hw2l : Function.update (Function.update w z (a0 + a1)) o (a0 - a1) l = w l := by
        rw [Function.update_of_ne hlo, Function.update_of_ne hlz]
      have hjodd : GOdd (Function.update (Function.update w z (a0 + a1)) o (a0 - a1) j) := by
        rw [hw2j]; exact hj
      have hrp : IsPivot (sem n (Gen.K z o hzo) * s) p :=
        isPivot_sem hp hxK (by rw [← col_sem]; exact ne_ev_of_odd hw2 hpos ⟨j, hjodd⟩ p)
      have hsame : (GOdd (a0 + a1) ↔ GOdd (a0 - a1)) := by
        rw [GOdd_add, GOdd_sub]
      by_cases hodd : GOdd (a0 + a1)
      · -- the new entries `0, 1` are the first odd ones: retrograde
        have hf2 : FirstTwo (Function.update (Function.update w z (a0 + a1)) o (a0 - a1)) z o := by
          refine ⟨hzo, ?_, ?_, ?_, ?_⟩
          · rw [Function.update_of_ne hzo.ne, Function.update_self]; exact hodd
          · rw [Function.update_self]; exact hsame.1 hodd
          · intro x hx; exact absurd hx (by have := Fin.lt_def.1 hx; omega)
          · intro x hx hx'
            exact absurd hx' (by have := Fin.lt_def.1 hx; have := Fin.lt_def.1 hx'; omega)
        refine step_retro' hrp.ne_one (u := K z o hzo ^ 7 * i o ^ 0) ?_ ?_
        · rw [syl_eq hrp, sylCol_K hw2 hpos (lde_of_odd hw2 z hf2.2.1) hf2,
            K_congr hf2.1 hzo rfl rfl, Function.update_of_ne hzo.ne, Function.update_self,
            Function.update_self, qexp_add_sub]
        · simp only [map_mul, map_pow, cl_K, cl_ofK, cl_i, pow_zero, mul_one]
          exact gK_pow_seven_mul z o hzo
      · -- disjoint
        have hf2 : FirstTwo (Function.update (Function.update w z (a0 + a1)) o (a0 - a1)) j l := by
          refine ⟨hjl, hjodd, by rw [hw2l]; exact hl, ?_, ?_⟩
          · intro x hx
            rw [Function.update_apply, Function.update_apply]
            split_ifs
            · exact fun h => hodd (hsame.2 h)
            · exact hodd
            · exact hbefore x hx
          · intro x hx hx'
            rw [Function.update_of_ne (hoj.trans hx).ne', Function.update_of_ne (hzj.trans hx).ne']
            exact hbetween x hx hx'
        have hsylr : syl (sem n (Gen.K z o hzo) * s) = syl s := by
          rw [syl_eq hrp, syl_eq hp, sylCol_K hw2 hpos (lde_of_odd hw2 j hjodd) hf2,
            sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩, K_congr hf2.1 hjl rfl rfl, hw2j,
            hw2l]
        have hset : oddSet (Function.update (Function.update w z (a0 + a1)) o (a0 - a1)) =
            oddSet w := by
          ext x
          simp only [mem_oddSet]
          rw [Function.update_apply, Function.update_apply]
          split_ifs with h1 h2
          · rw [h1]; exact iff_of_false (fun h => hodd (hsame.2 h)) (hbefore o hoj)
          · rw [h2]; exact iff_of_false hodd (hbefore z hzj)
          · rfl
        refine step_disj hs hrp.ne_one hsylr (by
          rw [level_eq hrp, level_eq hp, prof_eq hw2 (lde_of_odd hw2 j hjodd), prof_eq hw rfl,
            hset]) ?_ hstep
        rw [syl_eq hp, sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩]
        simp only [map_mul, map_pow, cl_K, cl_ofK, cl_i]
        have h1 : Commute (gK j l hjl) (gK z o hzo) :=
          e9 j l z o hjl hzo hjz hjo hlz hlo
        have h2 : Commute (gi l) (gK z o hzo) := e6 l z o hzo hlz hlo
        exact ((h1.pow_left 7).mul_left (h2.pow_left _)).eq

end


end QCert.BianSelingerUn
