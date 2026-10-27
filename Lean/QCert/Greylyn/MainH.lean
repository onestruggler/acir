/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the Main Lemma for the basic edge `H_[1,2]`

Case 1 of the proof of Lemma 31 (`H_[0,1]` with indices from `0`), by the
entries `u₀, u₁` of the numerator of the pivot column:

* both odd with residues differing by `z`: `z = 0` is Subcase 1.1 (the
  syllable of `s` is `H_[0,1]`); `z` odd is Subcases 1.2, 1.3: `(u₀ ± u₁)/δ`
  are odd of the same residue, the normal edge out of `r` is `H_[0,1]`, and
  the edge is retrograde; `z = 2` is Subcase 1.4, closed by (26) with
  `G' = X_[0,1] ω⁷_[1] ω_[0]`;
* one odd, one even: Subcase 1.5, retrograde;
* both even: Subcase 1.6, by the δ-valuation of `u₀ + u₁`: at least `3`
  (Subcase 1.6.1, `G' = H_[0,1]`, which commutes with the syllable), or
  exactly `2` or `1` (Subcases 1.6.2, 1.6.3, retrograde);
* `k = 0`, pivot column `ωᵐ e_c`: `c ∈ {0, 1}` is Subcases 1.7.2 and 1.8
  (retrograde), `c ≥ 2` is Subcase 1.9 (`G' = H_[0,1]`), and pivot `0` is
  Subcase 1.7.1 (retrograde through column `1`).

The thesis computes the pivot column of `r` in Subcase 1.7.2 as
`(√2 ωᶥ, √2 ωᶥ, 0, …)`; it is `(ωᶥ/√2, ωᶥ/√2, 0, …)`, which is what the
rest of the argument uses.
-/
import QCert.Greylyn.MainOmega

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem upd2_fst {f : Fin n → ZOmega} {a b : Fin n} (h : a ≠ b) (x y : ZOmega) :
    Function.update (Function.update f a x) b y a = x := by
  rw [Function.update_of_ne h, Function.update_self]

theorem upd2_snd {f : Fin n → ZOmega} {a b : Fin n} (x y : ZOmega) :
    Function.update (Function.update f a x) b y b = y := Function.update_self _ _ _

theorem upd2_other {f : Fin n → ZOmega} {a b c : Fin n} (hca : c ≠ a) (hcb : c ≠ b)
    (x y : ZOmega) : Function.update (Function.update f a x) b y c = f c := by
  rw [Function.update_of_ne hcb, Function.update_of_ne hca]

/-- `z < o` are the indices `0, 1`: then they are the first two odd entries
as soon as both are odd. -/
theorem firstTwo_01 {w : Fin n → ZOmega} {z o : Fin n} (h : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) (h1 : IsOdd (w z)) (h2 : IsOdd (w o)) : FirstTwo w z o :=
  ⟨h, h1, h2, fun a ha => absurd ha (by rw [Fin.lt_def]; omega),
    fun a h1 h2 => absurd h1 (by rw [Fin.lt_def] at h2 ⊢; omega)⟩

theorem retro_rel_H {z o : Fin n} (h : z < o) :
    Derivable (Rel n) (H z o h * ω z ^ 0 * FreeMonoid.of (Gen.H z o h)) 1 := by
  rw [derivable_iff]
  simp only [map_mul, map_one, cl_H, pow_zero, mul_one]
  exact e2 z o h

/-- A retrograde square for `H_[0,1]`: the normal edge out of `r` is
`H_[0,1]` (its first two odd entries `0, 1` have equal residues). -/
theorem retro_H {s : St n} (hs : s ≠ 1) {z o : Fin n} (h : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) {p : Fin n} (hp : IsPivot s p) (hop : o ≤ p) {K : ℕ}
    {w : Fin n → ZOmega} (hw : HasNum (col (sem n (Gen.H z o h) * s) p) K w) (hK : 0 < K)
    (h1 : IsOdd (w z)) (h2 : IsOdd (w o)) (h3 : res (w z) = res (w o)) :
    Square s (Gen.H z o h) := by
  have hf := firstTwo_01 h hz ho h1 h2
  have hgidx : ∀ i ∈ gidx (Gen.H z o h), i ≤ p := by
    intro i hi
    simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact h.le.trans hop
    · exact hop
  have hr : IsPivot (sem n (Gen.H z o h) * s) p := by
    refine isPivot_mul hp hgidx ?_
    rw [← sm_sem, ← col_mul]
    exact ne_ev_of_hasNum hw hK ⟨z, h1⟩ p
  have hsylr := syl_H_of' hr hw hK hf h
  have hz0 : zexp (w z) (w o) = 0 := by unfold zexp; rw [h3]; omega
  rw [hz0] at hsylr
  exact sq_retro hs hr.ne_one hsylr (retro_rel_H h)

/-- `H_[0,1]` commutes with a syllable on indices other than `0, 1`. -/
theorem comm_H_unit {z o : Fin n} (h : z < o) {c p : Fin n} (hcp : c < p) (hcz : c ≠ z)
    (hco : c ≠ o) (hpz : p ≠ z) (hpo : p ≠ o) (e : ℕ) :
    Commute (gH z o h) (gω p ^ e * gX c p hcp) :=
  ((c_ωH h hpz hpo).symm.pow_right e).mul_right (e8 z o c p h hcp hcz hco hpz hpo)

/-- Two states with the same pivot, the same least δ-exponent and odd
numerator entries at the same places have the same level. -/
theorem level_eq_of_odd {r s : St n} {p : Fin n} (hr : IsPivot r p) (hs : IsPivot s p) {K : ℕ}
    {w' w : Fin n → ZOmega} (hwr : HasNum (col r p) K w') (hws : HasNum (col s p) K w)
    {i0 : Fin n} (hodd : IsOdd (w i0)) (hiff : ∀ i, IsOdd (w' i) ↔ IsOdd (w i)) :
    level r = level s := by
  have hset : oddSet w' = oddSet w := by ext i; simp only [mem_oddSet, hiff]
  rw [level_eq hr, level_eq hs, prof_eq hwr (lde_eq hwr (Or.inr ⟨i0, (hiff i0).2 hodd⟩)),
    prof_eq hws (lde_eq hws (Or.inr ⟨i0, hodd⟩)), hset]

/-- Case 1 of the proof of Lemma 31: the basic edge `H_[0,1]`. -/
theorem square_H {s : St n} (hs : s ≠ 1) (z o : Fin n) (h : z < o) (hz : (z : ℕ) = 0)
    (ho : (o : ℕ) = 1) : Square s (Gen.H z o h) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  by_cases hpz : p = z
  · -- Subcase 1.7.1: the pivot is `0`; column `1` of `r` is `(e_0 - e_1)/√2`
    subst hpz
    have hcol' : col (sem n (Gen.H p o h) * s) o = col (sem n (Gen.H p o h)) o := by
      rw [col_mul, hp.2 o h, mulVec_ev]
    have hr : IsPivot (sem n (Gen.H p o h) * s) o := by
      refine ⟨by rw [hcol']; exact (isPivot_H h).1, fun q hq => ?_⟩
      rw [col_mul, hp.2 q (h.trans hq), sm_sem]
      apply mat_mulVec_ev_of_ne
      intro i hi
      simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ne_of_lt (h.trans hq)
      · exact ne_of_lt hq
    have hsylr : syl (sem n (Gen.H p o h) * s) = H p o h * ω p ^ 0 := by
      rw [syl_eq hr, hcol', ← syl_eq (isPivot_H h), syl_H h]
    exact sq_retro hs hr.ne_one hsylr (retro_rel_H h)
  have hop : o ≤ p := by
    rw [Fin.le_def]
    have : (p : ℕ) ≠ 0 := fun h' => hpz (Fin.ext (by omega))
    omega
  have hzo := h.ne
  obtain ⟨u, hu⟩ : ∃ u, HasNum (col s p) (lde (col s p)) u := ⟨_, hasNum_num s p⟩
  have hcolr : col (sem n (Gen.H z o h) * s) p = twoLevel z o Hmat *ᵥ col s p := by
    rw [col_mul, sm_sem]; rfl
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · -- `k = 0`
    rw [hk] at hu
    obtain ⟨c, hcp, hc1, hc0⟩ := unit_data' hp hu
    have hcodd : IsOdd (u c) := isOdd_of_nrm0_eq_one hc1
    by_cases hc : c = z ∨ c = o
    · -- Subcases 1.7.2 and 1.8: `H v` is `ωᵐ (e_0 ± e_1)/√2`, retrograde
      have hp' : ∀ x y : ZOmega, x + y = δz ^ 0 * (x + y) := fun x y => by rw [pow_zero, one_mul]
      have hm' : ∀ x y : ZOmega, x - y = δz ^ 0 * (x - y) := fun x y => by rw [pow_zero, one_mul]
      have hw := hasNum_H_gen hu hzo 0 (by omega) (hp' (u z) (u o)) (hm' (u z) (u o))
      rw [← hcolr] at hw
      have hpair : IsOdd (u z + u o) ∧ IsOdd (u z - u o) ∧ res (u z + u o) = res (u z - u o) := by
        rcases hc with rfl | rfl
        · exact pair_oe hcodd (by rw [hc0 o hzo.symm]; exact not_isOdd_zero)
        · exact pair_eo (by rw [hc0 z hzo]; exact not_isOdd_zero) hcodd
      obtain ⟨o1, o2, hres⟩ := hpair
      refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
      · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
      · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
      · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]
    · -- Subcase 1.9: `H_[0,1]` fixes the pivot column
      push Not at hc
      obtain ⟨hcz, hco⟩ := hc
      have hoc : o < c := by
        rw [Fin.lt_def]
        have h1 : (c : ℕ) ≠ 0 := fun h' => hcz (Fin.ext (by omega))
        have h2 : (c : ℕ) ≠ 1 := fun h' => hco (Fin.ext (by omega))
        omega
      have hvz : col s p z = 0 := by
        have := hu z; rw [pow_zero, one_mul, hc0 z (Ne.symm hcz), map_zero] at this; exact this
      have hvo : col s p o = 0 := by
        have := hu o; rw [pow_zero, one_mul, hc0 o (Ne.symm hco), map_zero] at this; exact this
      have hcol : col (sem n (Gen.H z o h) * s) p = col s p := by
        rw [hcolr]; exact twoLevel_mulVec_of_zero hzo _ hvz hvo
      have hpz' : p ≠ z := ne_of_gt (lt_of_lt_of_le (h.trans hoc) hcp)
      have hpo' : p ≠ o := ne_of_gt (lt_of_lt_of_le hoc hcp)
      have hr : IsPivot (sem n (Gen.H z o h) * s) p :=
        ⟨by rw [hcol]; exact hp.1, fun q hq => by
          rw [col_mul, hp.2 q hq, sm_sem]
          apply mat_mulVec_ev_of_ne
          intro i hi
          simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ne_of_lt (((h.trans hoc).trans_le hcp).trans hq)
          · exact ne_of_lt ((hoc.trans_le hcp).trans hq)⟩
      have hsylr : syl (sem n (Gen.H z o h) * s) = syl s := by
        rw [syl_eq hr, syl_eq hp, hcol]
      refine sq_gen hr.ne_one hsylr (G' := H z o h) ?_ ?_
      · rw [derivable_iff]
        simp only [map_mul, cl_H]
        have hcne : u c ≠ 0 := fun h' => by rw [h'] at hc1; simp [nrm0] at hc1
        rcases hcp.lt_or_eq with hcp' | hcp'
        · rw [syl_unit_lt_of hp hu hcne hc0 hcp']
          simp only [map_mul, map_pow, cl_ω, cl_X]
          exact (comm_H_unit h hcp' hcz hco hpz' hpo' _).eq.symm
        · have hc0' : ∀ a, a ≠ p → u a = 0 := hcp' ▸ hc0
          have hcne' : u p ≠ 0 := hcp' ▸ hcne
          rw [syl_unit_eq_of hp hu hcne' hc0']
          simp only [map_pow, cl_ω]
          exact ((c_ωH h hpz' hpo').symm.pow_right _).eq.symm
      · apply allBelow_A hp (t_above hp hk)
        refine AllL.of ?_
        intro i hi
        simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact (h.trans hoc).trans_le hcp
        · exact hoc.trans_le hcp
  · -- `k > 0`
    have hgidx : ∀ i ∈ gidx (Gen.H z o h), i ≤ p := by
      intro i hi
      simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact h.le.trans hop
      · exact hop
    obtain ⟨ht1, ht2⟩ := t_below hp hk
    by_cases hoz : IsOdd (u z)
    · by_cases hoo : IsOdd (u o)
      · -- both odd: Subcases 1.1–1.4
        have hf01 := firstTwo_01 h hz ho hoz hoo
        have hsyl := syl_H_of' hp hu hk hf01 h
        have := res_lt (u z)
        have := res_lt (u o)
        have hzdef : zexp (u z) (u o) = (res (u o) + 4 - res (u z)) % 4 := rfl
        rcases (show zexp (u z) (u o) = 0 ∨ zexp (u z) (u o) = 2 ∨
            (res (u z) + res (u o)) % 2 = 1 by omega) with h0 | h2 | hodd
        · -- Subcase 1.1: the syllable of `s` is `H_[0,1]`
          apply sq_triv hs
          rw [hsyl, h0, derivable_iff]
          simp only [cl_H, pow_zero, mul_one]
        · -- Subcase 1.4: `z = 2`, closed by (26)
          obtain ⟨e1, e2, he1, he2, o1, o2, hz2⟩ := pair_oo_two hoz hoo h2
          have hw := hasNum_H_gen hu hzo 2 le_rfl he1 he2
          rw [← hcolr] at hw
          have hw' : HasNum (col (sem n (Gen.H z o h) * s) p) (lde (col s p))
              (Function.update (Function.update (fun c => δz ^ (2 - 2) * u c) z (ηz * e1)) o
                (ηz * e2)) := hw
          have q1 : IsOdd (ηz * e1) := isOdd_mul isOdd_ηz o1
          have q2 : IsOdd (ηz * e2) := isOdd_mul isOdd_ηz o2
          have hf' := firstTwo_01 h hz ho (w := Function.update (Function.update
            (fun c => δz ^ (2 - 2) * u c) z (ηz * e1)) o (ηz * e2))
            (by rw [upd2_fst hzo]; exact q1) (by rw [upd2_snd]; exact q2)
          have hr : IsPivot (sem n (Gen.H z o h) * s) p := by
            refine isPivot_mul hp hgidx ?_
            rw [← sm_sem, ← col_mul]
            exact ne_ev_of_hasNum hw' hk ⟨z, hf'.2.1⟩ p
          have hsylr := syl_H_of' hr hw' hk hf' h
          rw [upd2_fst hzo, upd2_snd, zexp_mul_left isOdd_ηz o1 o2, hz2] at hsylr
          rw [h2] at hsyl
          refine sq_gen hr.ne_one hsylr (G' := X z o h * ω o ^ 7 * ω z) ?_ ?_
          · rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_H, cl_ω, cl_X]
            rw [e26 z o h]
            simp only [mul_assoc]
          · apply allBelow_B hp ht1 ht2
            refine ((AllL.of ?_).mul ((AllL.of ?_).pow 7)).mul (AllL.of ?_)
            · exact ⟨trivial, by simp [gidx, h.le.trans hop, hop]⟩
            · exact ⟨trivial, by simp [gidx, hop]⟩
            · exact ⟨trivial, by simp [gidx, h.le.trans hop]⟩
        · -- Subcases 1.2 and 1.3: `z` odd, retrograde
          obtain ⟨e1, e2, he1, he2, o1, o2, hres⟩ := pair_oo_odd hoz hoo hodd
          have hw := hasNum_H_gen hu hzo 1 (by omega) (by rw [pow_one]; exact he1)
            (by rw [pow_one]; exact he2)
          rw [← hcolr] at hw
          refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
          · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
          · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
          · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]
      · -- Subcase 1.5: `u₀` odd, `u₁` even, retrograde
        obtain ⟨o1, o2, hres⟩ := pair_oe hoz hoo
        have hw := hasNum_H_gen hu hzo 0 (by omega)
          (by rw [pow_zero, one_mul]) (by rw [pow_zero, one_mul])
        rw [← hcolr] at hw
        refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
        · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
        · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
        · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]
    · by_cases hoo : IsOdd (u o)
      · -- the note to Subcase 1.5: `u₀` even, `u₁` odd, retrograde
        obtain ⟨o1, o2, hres⟩ := pair_eo hoz hoo
        have hw := hasNum_H_gen hu hzo 0 (by omega)
          (by rw [pow_zero, one_mul]) (by rw [pow_zero, one_mul])
        rw [← hcolr] at hw
        refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
        · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
        · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
        · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]
      · -- Subcase 1.6: both even
        rcases pair_ee hoz hoo with ⟨⟨d1, hd1⟩, ⟨d2, hd2⟩⟩ |
            ⟨e1, e2, he1, he2, o1, o2, hres⟩ | ⟨e1, e2, he1, he2, o1, o2, hres⟩
        · -- Subcase 1.6.1: `δ³ ∣ u₀ ± u₁`, `G' = H_[0,1]`
          obtain ⟨α, β, hf, hβp⟩ := odd_data' hp hu hk rfl
          have hsyl := syl_H_of' hp hu hk hf hf.1
          have hw := hasNum_H_red hu hzo hd1 hd2
          rw [← hcolr] at hw
          have hαz : α ≠ z := fun h' => hoz (h' ▸ hf.2.1)
          have hαo : α ≠ o := fun h' => hoo (h' ▸ hf.2.1)
          have hβz : β ≠ z := fun h' => hoz (h' ▸ hf.2.2.1)
          have hβo : β ≠ o := fun h' => hoo (h' ▸ hf.2.2.1)
          have hiff : ∀ i, IsOdd (Function.update (Function.update u z (ηz * δz * d1)) o
              (ηz * δz * d2) i) ↔ IsOdd (u i) := by
            intro i
            by_cases hio : i = o
            · subst hio; rw [upd2_snd]
              exact iff_of_false (not_isOdd_ηz_δz_mul d2) hoo
            by_cases hiz : i = z
            · subst hiz; rw [upd2_fst hzo]
              exact iff_of_false (not_isOdd_ηz_δz_mul d1) hoz
            rw [upd2_other hiz hio]
          have hf' := hf.of_iff hiff
          have hr : IsPivot (sem n (Gen.H z o h) * s) p := by
            refine isPivot_mul hp hgidx ?_
            rw [← sm_sem, ← col_mul]
            exact ne_ev_of_hasNum hw hk ⟨α, hf'.2.1⟩ p
          have hsylr := syl_H_of' hr hw hk hf' hf.1
          rw [upd2_other hαz hαo, upd2_other hβz hβo, ← hsyl] at hsylr
          have hrel : Derivable (Rel n) (syl s * FreeMonoid.of (Gen.H z o h))
              (H z o h * syl s) := by
            rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_H, cl_ω]
            have c1 : Commute (gH z o h) (gH α β hf.1) := e7 z o α β h hf.1 hαz hαo hβz hβo
            have c2 : Commute (gH z o h) (gω α ^ zexp (u α) (u β)) :=
              (c_ωH h hαz hαo).symm.pow_right _
            exact (c1.mul_right c2).eq.symm
          have hlev : level (sem n (Gen.H z o h) * s) = level s :=
            level_eq_of_odd hr hp hw hu hf.2.1 hiff
          have hq : sem n (Gen.H z o h) * (⟪syl s⟫ * s) =
              ⟪syl (sem n (Gen.H z o h) * s)⟫ * (sem n (Gen.H z o h) * s) := by
            have := derivable_sound (fun _ _ h => sound h) hrel
            rw [map_mul, map_mul, FreeMonoid.lift_eval_of] at this
            rw [hsylr, ← mul_assoc, ← this, mul_assoc]
          refine sq_gen hr.ne_one hsylr (G' := H z o h) hrel ?_
          refine AllBelow.letter (level_syl_lt hs) ?_
          rw [hq]
          exact (level_syl_lt hr.ne_one).trans_eq hlev
        · -- Subcase 1.6.2: `u₀ ± u₁ = δ² e±`, retrograde
          have hw := hasNum_H_gen hu hzo 2 le_rfl he1 he2
          rw [← hcolr] at hw
          refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
          · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
          · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
          · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]
        · -- Subcase 1.6.3: `u₀ ± u₁ = δ e±`, retrograde
          have hw := hasNum_H_gen hu hzo 1 (by omega) (by rw [pow_one]; exact he1)
            (by rw [pow_one]; exact he2)
          rw [← hcolr] at hw
          refine retro_H hs h hz ho hp hop hw (by omega) ?_ ?_ ?_
          · rw [upd2_fst hzo]; exact isOdd_mul isOdd_ηz o1
          · rw [upd2_snd]; exact isOdd_mul isOdd_ηz o2
          · rw [upd2_fst hzo, upd2_snd, (res_mul isOdd_ηz o1).2, (res_mul isOdd_ηz o2).2, hres]

end

end QCert.Greylyn
