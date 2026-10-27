/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the Main Lemma for `G = X_[α,α+1]` at positive exponents

Case 3.2 of the proof of Lemma 3.7, writing `a = α`, `b = α + 1` and
`j < ℓ` for the first two odd entries of the numerator `w` of the pivot
column; `r = X_[α,α+1] s` has the numerator `w` with the entries `α`,
`α + 1` exchanged.
-/
import QCert.BianSelingerUn.MainX
import QCert.BianSelingerUn.Case3222

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem qexp_comm (x y : GaussianInt) : qexp x y = qexp y x := by
  unfold qexp; split_ifs <;> omega

/-- Case 3.2.2.2 with `w_{α+1}` odd: four odd entries `j < α < α+1 < ℓ'`. -/
theorem case_3222_odd {s : St n} (hs : s ≠ 1) {a b p : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) (hp : IsPivot s p) (hbp : b ≤ p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) (lde (col s p)) w) (hpos : 0 < lde (col s p)) {j : Fin n}
    (hf : FirstTwo w j a) (hbodd : GOdd (w b))
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.X a b hab) :=
  case_3222_odd' hs hab hb hp hbp hw hpos hf hbodd hstep

/-- Case 3.2: `α < p` and a positive exponent. -/
theorem main_X_pos {s : St n} (hs : s ≠ 1) {a b p : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) (hp : IsPivot s p) (hap : a < p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) (lde (col s p)) w) (hpos : 0 < lde (col s p))
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.X a b hab) := by
  have hbp : b ≤ p := Fin.le_def.2 (by have := Fin.lt_def.1 hap; omega)
  have hxX : ext (Gen.X a b hab) ≤ (p : ℕ) := hbp
  have hwX := hasNum_sem_X hw hab
  have hnot : ∀ x : Fin n, a < x → x < b → False := fun x h1 h2 => by
    have := Fin.lt_def.1 h1; have := Fin.lt_def.1 h2; omega
  obtain ⟨j, l, hf, hlp⟩ := pos_col hp hw hpos rfl
  obtain ⟨hjl, hj, hl, hbefore, hbetween⟩ := hf
  set wX := Function.update (Function.update w a (w b)) b (w a) with hwXdef
  have wXa : wX a = w b := by rw [hwXdef, Function.update_of_ne hab.ne, Function.update_self]
  have wXb : wX b = w a := by rw [hwXdef, Function.update_self]
  have wXo : ∀ x, x ≠ a → x ≠ b → wX x = w x := by
    intro x h1 h2; rw [hwXdef, Function.update_of_ne h2, Function.update_of_ne h1]
  have hsyl : syl s = K j l hjl ^ 7 * i l ^ qexp (w j) (w l) := by
    rw [syl_eq hp]; exact sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩
  have pivr : ∀ j', GOdd (wX j') → IsPivot (sem n (Gen.X a b hab) * s) p := fun j' h =>
    isPivot_sem hp hxX (by rw [← col_sem]; exact ne_ev_of_odd hwX hpos ⟨j', h⟩ p)
  have sylr : ∀ j' l' (hf' : FirstTwo wX j' l'),
      syl (sem n (Gen.X a b hab) * s) = K j' l' hf'.1 ^ 7 * i l' ^ qexp (wX j') (wX l') :=
    fun j' l' hf' => by
      rw [syl_eq (pivr j' hf'.2.1)]; exact sylCol_K hwX hpos (lde_of_odd hwX j' hf'.2.1) hf'
  have hmon : ∀ x ∈ FreeMonoid.toList (X a b hab), MonLetter p x := by
    intro x hx; simp only [X, FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx; exact hbp
  -- the disjoint cases
  have disj : a ≠ j → b ≠ j → a ≠ l → b ≠ l → FirstTwo wX j l → Step s (Gen.X a b hab) := by
    intro haj hbj hal hbl hf'
    have hrp := pivr j hf'.2.1
    refine step_disj hs hrp.ne_one ?_ (by rw [level_eq hrp, level_eq hp, prof_sem_X]) ?_ hstep
    · rw [sylr j l hf', hsyl, K_congr hf'.1 hjl rfl rfl, wXo j haj.symm hbj.symm,
        wXo l hal.symm hbl.symm]
    · rw [hsyl]
      simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i]
      have h1 : Commute (gK j l hjl) (gX a b hab) := (e8 a b j l hab hjl haj hal hbj hbl).symm
      have h2 : Commute (gi l) (gX a b hab) := e5 l a b hab hal.symm hbl.symm
      exact ((h1.pow_left 7).mul_left (h2.pow_left _)).eq
  -- squares whose `G'` is `X_[α,α+1]`
  have sq : ∀ j' l' (hjl' : j' < l') (hf' : FirstTwo wX j' l') (qq : ℕ),
      qexp (wX j') (wX l') = qq →
      cl (K j' l' hjl' ^ 7 * i l' ^ qq * FreeMonoid.of (Gen.X a b hab)) =
        cl (X a b hab * syl s) → Step s (Gen.X a b hab) := by
    intro j' l' hjl' hf' qq hqq hrel
    exact step_sq hs (pivr j' hf'.2.1).ne_one (X a b hab)
      (by rw [sylr j' l' hf', K_congr hf'.1 hjl' rfl rfl, hqq]; exact hrel)
      (allBelow_mon' hp hs hmon (Or.inl hpos)) hstep
  have low : ∀ x : Fin n, x < a → x ≠ a ∧ x ≠ b := fun x h => ⟨h.ne, (h.trans hab).ne⟩
  have high : ∀ x : Fin n, b < x → x ≠ a ∧ x ≠ b := fun x h => ⟨(hab.trans h).ne', h.ne'⟩
  have hcomm : ∀ l', l' ≠ a → l' ≠ b → Commute (gX a b hab) (gi l') :=
    fun l' h1 h2 => (e5 l' a b hab h1 h2).symm
  rcases lt_trichotomy l a with hla | hla | hla
  · ---- Case 3.2.2.1: `ℓ < α`, disjoint
    have hjo := low j (hjl.trans hla)
    have hlo := low l hla
    refine disj hjo.1.symm hjo.2.symm hlo.1.symm hlo.2.symm ⟨hjl, ?_, ?_, ?_, ?_⟩
    · rw [wXo j hjo.1 hjo.2]; exact hj
    · rw [wXo l hlo.1 hlo.2]; exact hl
    · intro x hx
      have := low x ((hx.trans hjl).trans hla)
      rw [wXo x this.1 this.2]; exact hbefore x hx
    · intro x hx hx'
      have := low x (hx'.trans hla)
      rw [wXo x this.1 this.2]; exact hbetween x hx hx'
  · ---- Case 3.2.2.2: `ℓ = α`
    rw [hla] at hjl hl hbetween hlp
    have hsyl := (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩)
    by_cases hbodd : GOdd (w b)
    · exact case_3222_odd hs hab hb hp hbp hw hpos ⟨hjl, hj, hl, hbefore, hbetween⟩ hbodd hstep
    · -- `w_{α+1}` even: by (14) and (10)
      have hjo := low j hjl
      have hf' : FirstTwo wX j b := by
        refine ⟨hjl.trans hab, by rw [wXo j hjo.1 hjo.2]; exact hj, by rw [wXb]; exact hl, ?_, ?_⟩
        · intro x hx
          have := low x (hx.trans hjl)
          rw [wXo x this.1 this.2]; exact hbefore x hx
        · intro x hx hx'
          by_cases hxa : x = a
          · rw [hxa, wXa]; exact hbodd
          · have hxa' : x < a := by
              rcases lt_trichotomy x a with h | h | h
              · exact h
              · exact absurd h hxa
              · exact (hnot x h hx').elim
            rw [wXo x hxa hx'.ne]; exact hbetween x hx hxa'
      refine sq j b (hjl.trans hab) hf' (qexp (w j) (w a)) (by rw [wXo j hjo.1 hjo.2, wXb]) ?_
      rw [hsyl]
      simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i, cl_X]
      exact ((((sc_XK_low j a b hjl hab).pow_right 7).mul_right
        ((sc_Xi a b hab).pow_right _)).eq).symm
  · have hbl : b ≤ l := Fin.le_def.2 (by have := Fin.lt_def.1 hla; omega)
    rcases eq_or_lt_of_le hbl with hbl' | hbl'
    · ---- `ℓ = α + 1`
      rw [← hbl'] at hjl hl hbetween hlp
      have hsyl := (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩)
      have hja : j ≤ a := Fin.le_def.2 (by have := Fin.lt_def.1 hjl; omega)
      rcases eq_or_lt_of_le hja with hja | hja
      · ---- Case 3.2.2.3: `j = α`, `ℓ = α + 1`
        rw [hja] at hj hbefore hbetween hjl
        have hsyl := (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩)
        have hf' : FirstTwo wX a b := by
          refine ⟨hab, by rw [wXa]; exact hl, by rw [wXb]; exact hj, ?_, ?_⟩
          · intro x hx
            have := low x hx
            rw [wXo x this.1 this.2]; exact hbefore x hx
          · intro x hx hx'; exact (hnot x hx hx').elim
        have hrp := pivr a hf'.2.1
        have hsylr : syl (sem n (Gen.X a b hab) * s) = K a b hab ^ 7 * i b ^ qexp (w a) (w b) := by
          rw [sylr a b hf', K_congr hf'.1 hab rfl rfl, wXa, wXb, qexp_comm]
        have hmon' : ∀ x ∈ FreeMonoid.toList (X a b hab * i a * i a * i a * i b),
            MonLetter p x := by
          intro x hx
          simp only [X, i, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
            List.mem_singleton] at hx
          rcases hx with ((((rfl | rfl) | rfl) | rfl) | rfl)
          all_goals first | exact hbp | exact hap.le
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (qexp_le (w a) (w b)) with hq | hq
        · -- `q = 0`: the inverse of (15)
          refine step_sq hs hrp.ne_one (i b * i b) ?_ (allBelow_mon' hp hs ?_ (Or.inl hpos)) hstep
          · rw [hsylr, hsyl, hq]
            simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i, pow_zero, mul_one]
            simp only [mul_assoc]
            simpa only [mul_one] using f15' a b hab 1
          · intro x hx
            simp only [i, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
              List.mem_singleton] at hx
            rcases hx with rfl | rfl <;> exact hbp
        · -- `q = 1`: (28)
          refine step_sq hs hrp.ne_one (X a b hab * i a * i a * i a * i b) ?_
            (allBelow_mon' hp hs hmon' (Or.inl hpos)) hstep
          rw [hsylr, hsyl, hq]
          simp only [map_mul, map_pow, cl_K, cl_ofX, cl_X, cl_i, pow_one]
          simp only [mul_assoc]
          simpa only [mul_one] using f28 a b hab 1
      · ---- Case 3.2.2.4: `j < α`, `ℓ = α + 1`: by (14) and (10)
        have hjo := low j hja
        have hf' : FirstTwo wX j a := by
          refine ⟨hja, by rw [wXo j hjo.1 hjo.2]; exact hj, by rw [wXa]; exact hl, ?_, ?_⟩
          · intro x hx
            have := low x (hx.trans hja)
            rw [wXo x this.1 this.2]; exact hbefore x hx
          · intro x hx hx'
            have := low x hx'
            rw [wXo x this.1 this.2]; exact hbetween x hx (hx'.trans hab)
        refine sq j a hja hf' (qexp (w j) (w b)) (by rw [wXo j hjo.1 hjo.2, wXa]) ?_
        rw [hsyl]
        simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i, cl_X]
        exact ((((sc_XK_low' j a b hja hab).pow_right 7).mul_right
          ((sc_Xi' a b hab).pow_right _)).eq).symm
    · ---- `ℓ > α + 1`
      have hlo := high l hbl'
      rcases lt_trichotomy j a with hja | hja | hja
      · ---- Case 3.2.2.5: `j < α`, disjoint
        have hjo := low j hja
        refine disj hjo.1.symm hjo.2.symm hlo.1.symm hlo.2.symm ⟨hjl, ?_, ?_, ?_, ?_⟩
        · rw [wXo j hjo.1 hjo.2]; exact hj
        · rw [wXo l hlo.1 hlo.2]; exact hl
        · intro x hx
          have := low x (hx.trans hja)
          rw [wXo x this.1 this.2]; exact hbefore x hx
        · intro x hx hx'
          by_cases hxa : x = a
          · rw [hxa, wXa]; exact hbetween b (hja.trans hab) hbl'
          by_cases hxb : x = b
          · rw [hxb, wXb]; exact hbetween a hja (hab.trans hbl')
          rw [wXo x hxa hxb]; exact hbetween x hx hx'
      · ---- Case 3.2.2.6: `j = α`: by (13)
        rw [hja] at hj hbefore hbetween hjl
        have hsyl := (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩)
        have hwb : ¬ GOdd (w b) := hbetween b hab hbl'
        have hf' : FirstTwo wX b l := by
          refine ⟨hbl', by rw [wXb]; exact hj, by rw [wXo l hlo.1 hlo.2]; exact hl, ?_, ?_⟩
          · intro x hx
            by_cases hxa : x = a
            · rw [hxa, wXa]; exact hwb
            · have hxa' : x < a := by
                rcases lt_trichotomy x a with h | h | h
                · exact h
                · exact absurd h hxa
                · exact (hnot x h hx).elim
              rw [wXo x hxa hx.ne]; exact hbefore x hxa'
          · intro x hx hx'
            have := high x hx
            rw [wXo x this.1 this.2]; exact hbetween x (hab.trans hx) hx'
        refine sq b l hbl' hf' (qexp (w a) (w l)) (by rw [wXb, wXo l hlo.1 hlo.2]) ?_
        rw [hsyl]
        simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i, cl_X]
        exact ((((sc_XK_high a b l hab hbl').pow_right 7).mul_right
          ((hcomm l hlo.1 hlo.2).pow_right _)).eq).symm
      rcases eq_or_lt_of_le (show b ≤ j from Fin.le_def.2 (by
        have := Fin.lt_def.1 hja; omega)) with hjb | hjb
      · ---- Case 3.2.2.7: `j = α + 1`: by (13)
        rw [← hjb] at hj hbefore hbetween hjl
        have hsyl := (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hjl, hj, hl, hbefore, hbetween⟩)
        have hwa : ¬ GOdd (w a) := hbefore a hab
        have hf' : FirstTwo wX a l := by
          refine ⟨hab.trans hbl', by rw [wXa]; exact hj, by rw [wXo l hlo.1 hlo.2]; exact hl, ?_, ?_⟩
          · intro x hx
            have := low x hx
            rw [wXo x this.1 this.2]; exact hbefore x (hx.trans hab)
          · intro x hx hx'
            by_cases hxb : x = b
            · rw [hxb, wXb]; exact hwa
            · have hbx : b < x := by
                rcases lt_trichotomy x b with h | h | h
                · exact (hnot x hx h).elim
                · exact absurd h hxb
                · exact h
              rw [wXo x hx.ne' hxb]; exact hbetween x hbx hx'
        refine sq a l (hab.trans hbl') hf' (qexp (w b) (w l)) (by rw [wXa, wXo l hlo.1 hlo.2]) ?_
        rw [hsyl]
        simp only [map_mul, map_pow, cl_K, cl_ofX, cl_i, cl_X]
        exact ((((sc_XK_high' a b l hab hbl').pow_right 7).mul_right
          ((hcomm l hlo.1 hlo.2).pow_right _)).eq).symm
      · ---- Case 3.2.2.8: `j > α + 1`, disjoint
        have hjo := high j hjb
        refine disj hjo.1.symm hjo.2.symm hlo.1.symm hlo.2.symm ⟨hjl, ?_, ?_, ?_, ?_⟩
        · rw [wXo j hjo.1 hjo.2]; exact hj
        · rw [wXo l hlo.1 hlo.2]; exact hl
        · intro x hx
          by_cases hxa : x = a
          · rw [hxa, wXa]; exact hbefore b hjb
          by_cases hxb : x = b
          · rw [hxb, wXb]; exact hbefore a (hab.trans hjb)
          rw [wXo x hxa hxb]; exact hbefore x hx
        · intro x hx hx'
          have := high x (hjb.trans hx)
          rw [wXo x this.1 this.2]; exact hbetween x hx hx'

/-- Case 3 of the proof of Lemma 3.7: `G = X_[α,α+1]`. -/
theorem main_X {s : St n} (hs : s ≠ 1) {a b : Fin n} (hab : a < b) (hb : (b : ℕ) = a + 1)
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.X a b hab) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  by_cases hpa : p ≤ a
  · ---- Cases 3.1.1, 3.2.1: `α ≥ p`, retrograde
    exact step_X_low hab (fun q hq => hp.2 q (lt_of_le_of_lt hpa hq))
  push Not at hpa
  obtain ⟨w, hw⟩ := lde_spec (hasNum_exists s p)
  rcases Nat.eq_zero_or_pos (lde (col s p)) with h0 | hpos
  · rw [h0] at hw; exact main_X_unit hs hab hb hp hpa hw hstep
  · exact main_X_pos hs hab hb hp hpa hw hpos hstep

end

end QCert.BianSelingerUn
