/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the Main Lemma for `G = X_[α,α+1]` (Case 3)

Case 3 of the proof of Lemma 3.7, writing `a = α`, `b = α + 1`.  If `α ≥ p`
the edge is retrograde (3.1.1, 3.2.1).  Otherwise, at exponent `0` with the
pivot column `u e_c` (3.1.2, 3.1.3) the squares come from (10), (24), (25)
or are disjoint; at a positive exponent with first odd entries `j < ℓ`
(3.2.2) they come from (13), (14), (10), from (15) and (28) when
`{j, ℓ} = {α, α+1}`, or are disjoint — except Case 3.2.2.2 with
`w_{α+1}` odd, which has four odd entries (`case_3222_odd`).
-/
import QCert.BianSelingerUn.MainK
import QCert.BianSelingerUn.Derived2

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem gX_pow_conj (a b : Fin n) (hab : a < b) (e : ℕ) :
    gX a b hab * gi a ^ e * gX a b hab = gi b ^ e := by
  rw [((sc_Xi a b hab).pow_right e).eq, mul_assoc, e2, mul_one]

/-! ### Exponent `0` -/

/-- Case 3.1 with `α < p`: the pivot column of `s` is `u e_c`. -/
theorem main_X_unit {s : St n} (hs : s ≠ 1) {a b p : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) (hp : IsPivot s p) (hap : a < p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) 0 w)
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.X a b hab) := by
  have hbp : b ≤ p := Fin.le_def.2 (by have := Fin.lt_def.1 hap; omega)
  have hxX : ext (Gen.X a b hab) ≤ (p : ℕ) := hbp
  have hwX := hasNum_sem_X hw hab
  obtain ⟨c, hc1, hc0, hcp⟩ := unit_col hp hw
  have hcne := ne_zero_of_norm hc1
  have hnot : ∀ x : Fin n, a < x → x < b → False := fun x h1 h2 => by
    have := Fin.lt_def.1 h1; have := Fin.lt_def.1 h2; omega
  have hab' : a ≠ b := hab.ne
  by_cases hca : c = a
  · ---- `c = α`
    rw [hca] at hc1 hc0 hcne hcp
    have hsyl : syl s = X a p hap * i a ^ expo (w a) := by
      rw [syl_eq hp, sylCol_unit_lt hw hcne hc0 hap]
    have hz' : ∀ x, x ≠ b →
        Function.update (Function.update w a (w b)) b (w a) x = 0 := by
      intro x hx
      rw [Function.update_of_ne hx, Function.update_apply]
      split_ifs with h
      · exact hc0 b hab'.symm
      · exact hc0 x h
    have hne' : Function.update (Function.update w a (w b)) b (w a) b ≠ 0 := by
      rw [Function.update_self]; exact hcne
    rcases lt_or_eq_of_le hbp with hbp' | hbp'
    · ---- Case 3.1.3.1: `α ≤ p - 2`, `j = α`
      have hrp : IsPivot (sem n (Gen.X a b hab) * s) p := by
        refine isPivot_sem hp hxX (fun heq => hne' ?_)
        rw [← col_sem] at heq
        have := hwX b
        rw [heq, pow_zero, one_mul] at this
        simp only [ev, if_neg hbp'.ne] at this
        exact GaussianInt.toComplex_eq_zero.1 this.symm
      have hsylr : syl (sem n (Gen.X a b hab) * s) = X b p hbp' * i b ^ expo (w a) := by
        rw [syl_eq hrp, sylCol_unit_lt hwX hne' hz' hbp', Function.update_self]
      refine step_sq hs hrp.ne_one (X a b hab) ?_ (allBelow_mon' hp hs ?_ (Or.inr ?_)) hstep
      · -- (25)
        rw [hsylr, hsyl]
        simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
        simp only [mul_assoc]
        conv_lhs => rw [(((sc_Xi a b hab).pow_right _).eq).symm, ← mul_assoc,
          (sc_XX a b p hab hbp').eq.symm, mul_assoc]
      · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
        exact hbp
      · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
        simp only [Touches, not_or]; exact ⟨hap.ne, hbp'.ne⟩
    · ---- Case 3.1.2.2: `α = p - 1`, `j = α`
      subst hbp'
      by_cases hu : w a = 1
      · -- `e = 0`: `r = X_[α,α+1] s` is below `s`
        refine step_sq0 hs 1 ?_ (allBelow_one (level_syl_lt hs)) hstep
        rw [hsyl, hu, one_mul]
        simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
        simp [expo]
      · have hrp : IsPivot (sem n (Gen.X a b hab) * s) b := by
          refine isPivot_sem hp hxX (fun heq => hu ?_)
          rw [← col_sem] at heq
          have := hwX b
          rw [heq, Function.update_self, pow_zero, one_mul] at this
          simp only [ev] at this
          exact GaussianInt.toComplex_inj.1 (this.symm.trans GaussianInt.toComplex_one.symm)
        have hsylr : syl (sem n (Gen.X a b hab) * s) = i b ^ expo (w a) := by
          rw [syl_eq hrp, sylCol_unit_eq hwX hne' hz', Function.update_self]
        refine step_sq hs hrp.ne_one 1 ?_ (allBelow_one (level_syl_lt hs)) hstep
        -- (10)
        rw [hsylr, hsyl, one_mul]
        simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
        exact ((sc_Xi a b hab).pow_right _).eq.symm
  by_cases hcb : c = b
  · ---- `c = α + 1`
    rw [hcb] at hc1 hc0 hcne hcp
    have hz' : ∀ x, x ≠ a →
        Function.update (Function.update w a (w b)) b (w a) x = 0 := by
      intro x hx
      rw [Function.update_apply, Function.update_of_ne hx]
      split_ifs with h
      · exact hc0 a hab'
      · exact hc0 x h
    have hne' : Function.update (Function.update w a (w b)) b (w a) a ≠ 0 := by
      rw [Function.update_of_ne hab', Function.update_self]; exact hcne
    have hrp : IsPivot (sem n (Gen.X a b hab) * s) p := by
      refine isPivot_sem hp hxX (fun heq => hne' ?_)
      rw [← col_sem] at heq
      have := hwX a
      rw [heq, pow_zero, one_mul] at this
      simp only [ev, if_neg hap.ne] at this
      exact GaussianInt.toComplex_eq_zero.1 this.symm
    have hsylr : syl (sem n (Gen.X a b hab) * s) = X a p hap * i a ^ expo (w b) := by
      rw [syl_eq hrp, sylCol_unit_lt hwX hne' hz' hap, Function.update_of_ne hab',
        Function.update_self]
    rcases lt_or_eq_of_le hbp with hbp' | hbp'
    · ---- Case 3.1.3.2: `α ≤ p - 2`, `j = α + 1`
      have hsyl : syl s = X b p hbp' * i b ^ expo (w b) := by
        rw [syl_eq hp, sylCol_unit_lt hw hcne hc0 hbp']
      refine step_sq hs hrp.ne_one (X a b hab) ?_ (allBelow_mon' hp hs ?_ (Or.inr ?_)) hstep
      · -- (25) and (2)
        rw [hsylr, hsyl]
        simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
        simp only [mul_assoc]
        conv_lhs => rw [(((sc_Xi' a b hab).pow_right _).eq).symm, ← mul_assoc,
          (sc_XX' a b p hab hbp').eq.symm, mul_assoc]
      · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
        exact hbp
      · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
        simp only [Touches, not_or]; exact ⟨hap.ne, hbp'.ne⟩
    · ---- Case 3.1.2.1: `α = p - 1`, `j = α + 1`
      subst hbp'
      have hsyl : syl s = i b ^ expo (w b) := by rw [syl_eq hp, sylCol_unit_eq hw hcne hc0]
      refine step_sq hs hrp.ne_one 1 ?_ (allBelow_one (level_syl_lt hs)) hstep
      -- (10) and (2)
      rw [hsylr, hsyl, one_mul]
      simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
      exact gX_pow_conj a b hab _
  · ---- `c ∉ {α, α+1}`
    have hwa : w a = 0 := hc0 a (Ne.symm hca)
    have hwb : w b = 0 := hc0 b (Ne.symm hcb)
    have hwX' : HasNum (col (sem n (Gen.X a b hab) * s) p) 0 w := by
      have e : Function.update (Function.update w a (w b)) b (w a) = w := by
        funext x
        rw [Function.update_apply, Function.update_apply]
        split_ifs with h1 h2
        · rw [h1, hwa, hwb]
        · rw [h2, hwa, hwb]
        · rfl
      rw [e] at hwX; exact hwX
    have hcol : col (sem n (Gen.X a b hab) * s) p = col s p := hwX'.eq_of hw
    have hrp : IsPivot (sem n (Gen.X a b hab) * s) p :=
      isPivot_sem hp hxX (by rw [← col_sem, hcol]; exact hp.1)
    have hsylr : syl (sem n (Gen.X a b hab) * s) = syl s := by rw [syl_eq hrp, syl_eq hp, hcol]
    rcases lt_or_eq_of_le hcp with hcp' | hcp'
    · by_cases hcb' : b = p
      · ---- Case 3.1.2.3: `α = p - 1`, `j < α`
        subst hcb'
        have hcpa : c < a := by
          rcases lt_trichotomy c a with h | h | h
          · exact h
          · exact absurd h hca
          · exact absurd hcp' (fun h' => hnot c h h')
        have hsyl : syl s = X c b hcp' * i c ^ expo (w c) := by
          rw [syl_eq hp, sylCol_unit_lt hw hcne hc0 hcp']
        refine step_sq hs hrp.ne_one (X c a hcpa) ?_ (allBelow_mon' hp hs ?_ (Or.inr ?_)) hstep
        · -- (24)
          rw [hsylr, hsyl]
          simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
          rw [← mul_assoc]
          exact f24 c a b hcpa hab (expo (w c))
        · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
          exact hap.le
        · intro x hx; simp only [FreeMonoid.toList_of, List.mem_singleton] at hx; subst hx
          simp only [Touches, not_or]; exact ⟨hcp'.ne, hab.ne⟩
      · ---- Case 3.1.3.3 with `j < p`: disjoint
        have hbp' : b < p := lt_of_le_of_ne hbp hcb'
        refine step_disj hs hrp.ne_one hsylr (by rw [level_eq hrp, level_eq hp, hcol]) ?_ hstep
        rw [syl_eq hp, sylCol_unit_lt hw hcne hc0 hcp']
        simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
        have h1 : Commute (gX c p hcp') (gX a b hab) :=
          e7 c p a b hcp' hab hca hcb hap.ne' hbp'.ne'
        have h2 : Commute (gi c) (gX a b hab) := e5 c a b hab hca hcb
        exact (h1.mul_left (h2.pow_left _)).eq
    · ---- Case 3.1.3.3 with `j = p`: disjoint
      rw [hcp'] at hcne hc0 hca hcb
      have hbp' : b < p := lt_of_le_of_ne hbp (Ne.symm hcb)
      refine step_disj hs hrp.ne_one hsylr (by rw [level_eq hrp, level_eq hp, hcol]) ?_ hstep
      rw [syl_eq hp, sylCol_unit_eq hw hcne hc0]
      simp only [map_mul, map_pow, cl_X, cl_ofX, cl_i]
      exact (Commute.pow_left (e5 p a b hab hca hcb) _).eq

end

end QCert.BianSelingerUn
