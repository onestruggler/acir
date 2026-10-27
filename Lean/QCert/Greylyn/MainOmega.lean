/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the Main Lemma for the basic edge `ω_[1]`

Case 2 of the proof of Lemma 31 (`ω_[0]` with indices from `0`):

* Subcase 2.1: the first odd entry of the pivot column is the entry `0`,
  `N = H_[0,α] ω^z_[0]`.  Then `ω_[0]` adds `1` to its residue, so the
  normal edge out of `r` is `H_[0,α] ω^{z-1}_[0]`, which is `N` after
  `ω_[0]` ("almost retrograde"), unless `z = 0`.  For `z = 0` the thesis
  uses `H_[0,α] ω⁴_[0] ≈ X_[0,α] H_[0,α]` and `G' = X_[0,α]`; but that
  equation is false (`H ω⁴_[j] = -X H`, see `eH4`), and the square closes
  with `G' = ω⁴_[0] ω⁴_[α] X_[0,α]` instead.
* Subcase 2.2: the entry `0` is even; the normal edges agree and
  `G' = ω_[0]` commutes with them.
* Subcase 2.3: the pivot column is `ωᵐ e_0`; the normal edge out of `r` is
  `N` after `ω_[0]`, or `r = I` when `m = 7` (then `N = ω_[0]`).
* Subcase 2.4: the pivot column is `ωᵐ e_c`, `c ≠ 0`; the normal edges
  agree and `G' = ω_[0]`.
-/
import QCert.Greylyn.Square

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-! ### Powers of `ω` -/

theorem nrm0_ωz_mul (x : ZOmega) : nrm0 (ωz * x) = nrm0 x := by
  rw [ωz_mul]; simp only [nrm0]; ring

theorem ωz_pow_mod (a : ℕ) : ωz ^ a = ωz ^ (a % 8) := by
  conv_lhs => rw [← Nat.mod_add_div a 8, pow_add, pow_mul, ωz_pow_eight, one_pow, mul_one]

theorem ωz_pow_inj {a b : ℕ} (h : ωz ^ a = ωz ^ b) : a % 8 = b % 8 := by
  rw [ωz_pow_mod a, ωz_pow_mod b] at h
  have key : ∀ i j : Fin 8, ωz ^ (i : ℕ) = ωz ^ (j : ℕ) → i = j := by decide +kernel
  exact congrArg Fin.val (key ⟨a % 8, Nat.mod_lt _ (by omega)⟩ ⟨b % 8, Nat.mod_lt _ (by omega)⟩ h)

theorem uexp_ωz_mul {x : ZOmega} (h : nrm0 x = 1) : uexp (ωz * x) % 8 = (uexp x + 1) % 8 := by
  apply ωz_pow_inj
  rw [ωz_pow_uexp (by rw [nrm0_ωz_mul]; exact h), pow_succ', ωz_pow_uexp h]

theorem gω_pow_congr (j : Fin n) {a b : ℕ} (h : a % 8 = b % 8) : gω j ^ a = gω j ^ b := by
  rw [gω_pow_mod j a, gω_pow_mod j b, h]

/-- `ω^{8-m'} ω ≈ ω^{8-m}` when `ω^{m'} = ω^{m+1}`. -/
theorem gω_pow_sub_succ (j : Fin n) {m m' : ℕ} (hm : m ≤ 8) (hm' : 1 ≤ m' ∧ m' ≤ 8)
    (h : m' % 8 = (m + 1) % 8) : gω j ^ (8 - m') * gω j = gω j ^ (8 - m) := by
  rw [← pow_succ]; exact gω_pow_congr j (by omega)

/-! ### The numerator after `ω_[0]` -/

theorem FirstTwo.of_iff {w w' : Fin n → ZOmega} {a b : Fin n} (hf : FirstTwo w a b)
    (h : ∀ i, IsOdd (w' i) ↔ IsOdd (w i)) : FirstTwo w' a b :=
  ⟨hf.1, (h a).2 hf.2.1, (h b).2 hf.2.2.1, fun i hi => by rw [h]; exact hf.2.2.2.1 i hi,
    fun i h1 h2 => by rw [h]; exact hf.2.2.2.2 i h1 h2⟩

theorem isOdd_update_ωz (u : Fin n → ZOmega) (j i : Fin n) :
    IsOdd (Function.update u j (ωz * u j) i) ↔ IsOdd (u i) := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, isOdd_ωz_mul]
  · rw [Function.update_of_ne hi]

theorem unit_data' {s : St n} {p : Fin n} (hp : IsPivot s p) {u : Fin n → ZOmega}
    (hu : HasNum (col s p) 0 u) : ∃ c, c ≤ p ∧ nrm0 (u c) = 1 ∧ ∀ a, a ≠ c → u a = 0 := by
  obtain ⟨c, hc1, hc0⟩ := unit_of_sum (col_unit s p) hu
  refine ⟨c, ?_, hc1, hc0⟩
  by_contra h
  have := hasNum_zero_of_entry hp hu (not_le.1 h)
  rw [this] at hc1; simp [nrm0] at hc1

theorem odd_data' {s : St n} {p : Fin n} (hp : IsPivot s p) {K : ℕ} {u : Fin n → ZOmega}
    (hu : HasNum (col s p) K u) (hK : 0 < K) (hl : lde (col s p) = K) :
    ∃ a b, FirstTwo u a b ∧ b ≤ p := by
  have hev := even_card_odd (col_unit s p) hu hK
  obtain ⟨j0, hj0⟩ := exists_odd (hl ▸ hu) (hl ▸ hK)
  have h2 : 2 ≤ (oddSet u).card := by
    have : 0 < (oddSet u).card := Finset.card_pos.2 ⟨j0, mem_oddSet.2 hj0⟩
    have hev' : Even (oddSet u).card := hev
    obtain ⟨r, hr⟩ := hev'
    omega
  obtain ⟨a, b, hf⟩ := exists_firstTwo h2
  refine ⟨a, b, hf, ?_⟩
  by_contra h
  have := hasNum_zero_of_entry hp hu (not_le.1 h)
  have h3 := hf.2.2.1
  rw [this] at h3; exact not_isOdd_zero h3

/-- `syl_H_of` with the order of the two indices given separately, so that
the numerator can be rewritten. -/
theorem syl_H_of' {r : St n} {p : Fin n} (hr : IsPivot r p) {K : ℕ} {w : Fin n → ZOmega}
    (hw : HasNum (col r p) K w) (hK : 0 < K) {a b : Fin n} (hf : FirstTwo w a b) (hab : a < b) :
    syl r = H a b hab * ω a ^ zexp (w a) (w b) :=
  syl_H_of hr hw hK hf

theorem ωz_mul_ne_zero {x : ZOmega} (h : x ≠ 0) : ωz * x ≠ 0 :=
  mul_ne_zero (by decide) h

/-- A numerator at exponent `0` equal to `e_p` gives the column `e_p`, and
conversely. -/
theorem num_eq_ev {v : Fin n → ℂ} {w : Fin n → ZOmega} (h : HasNum v 0 w) {p : Fin n}
    (hv : v = ev p) (a : Fin n) : w a = if a = p then 1 else 0 := by
  have := (h.unique (hv ▸ hasNum_ev p))
  exact congrFun this a

/-! ### Letters of words -/

/-- Every letter of `w` satisfies `P`. -/
def AllL (P : Gen n → Prop) (w : Word (Gen n)) : Prop := ∀ y ∈ FreeMonoid.toList w, P y

theorem AllL.of {P : Gen n → Prop} {y : Gen n} (h : P y) : AllL P (FreeMonoid.of y) := by
  intro z hz; rw [FreeMonoid.toList_of, List.mem_singleton] at hz; subst hz; exact h

theorem AllL.one {P : Gen n → Prop} : AllL P (1 : Word (Gen n)) := by
  intro z hz; simp at hz

theorem AllL.mul {P : Gen n → Prop} {w v : Word (Gen n)} (hw : AllL P w) (hv : AllL P v) :
    AllL P (w * v) := by
  intro z hz
  rw [FreeMonoid.toList_mul, List.mem_append] at hz
  rcases hz with hz | hz
  · exact hw z hz
  · exact hv z hz

theorem AllL.pow {P : Gen n → Prop} {w : Word (Gen n)} (hw : AllL P w) (k : ℕ) :
    AllL P (w ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact AllL.one
  | succ k ih => rw [pow_succ]; exact ih.mul hw

/-! ### Case 2 -/

/-- Case 2 of the proof of Lemma 31: the basic edge `ω_[0]`. -/
theorem square_ω {s : St n} (hs : s ≠ 1) (j : Fin n) (hj : (j : ℕ) = 0) :
    Square s (Gen.ω j) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  have hjp : j ≤ p := Fin.le_def.2 (by omega)
  obtain ⟨u, hu⟩ : ∃ u, HasNum (col s p) (lde (col s p)) u := ⟨_, hasNum_num s p⟩
  have hcolr : col (sem n (Gen.ω j) * s) p = oneLevel j QCert.ω *ᵥ col s p := by
    rw [col_mul, sm_sem]; rfl
  have hur : HasNum (col (sem n (Gen.ω j) * s) p) (lde (col s p))
      (Function.update u j (ωz * u j)) := by
    rw [hcolr]; exact hasNum_ω1 hu j
  have hgidx : ∀ i ∈ gidx (Gen.ω j), i ≤ p := by
    intro i hi; simp only [gidx, List.mem_singleton] at hi; rw [hi]; exact hjp
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · -- `k = 0`: Subcases 2.3 and 2.4
    rw [hk] at hu hur
    obtain ⟨c, hcp, hc1, hc0⟩ := unit_data' hp hu
    have hcne : u c ≠ 0 := fun h => by rw [h] at hc1; simp [nrm0] at hc1
    by_cases hcj : c = j
    · -- Subcase 2.3: the pivot column is `ωᵐ e_0`
      have hc1' : nrm0 (u j) = 1 := hcj ▸ hc1
      have hc0' : ∀ a, a ≠ j → u a = 0 := hcj ▸ hc0
      have hcne' : u j ≠ 0 := hcj ▸ hcne
      have hm := uexp_le (u j)
      have hm1 := one_le_uexp (u j)
      have hm' := uexp_le (ωz * u j)
      have hm1' := one_le_uexp (ωz * u j)
      have hmm := uexp_ωz_mul hc1'
      have hur1 : Function.update u j (ωz * u j) j ≠ 0 := by
        rw [Function.update_self]; exact ωz_mul_ne_zero hcne'
      have hur0 : ∀ a, a ≠ j → Function.update u j (ωz * u j) a = 0 := by
        intro a ha; rw [Function.update_of_ne ha]; exact hc0' a ha
      clear hc1 hc0 hcne hcj
      by_cases hpj : p = j
      · subst j
        have hsyl := syl_unit_eq_of hp hu hcne' hc0'
        by_cases h7 : uexp (u p) = 7
        · -- `r = I`: the syllable of `s` is `ω_[0]` itself
          apply sq_triv hs
          rw [hsyl, h7]
          simpa using Derivable.refl (Γ := Rel n) (FreeMonoid.of (Gen.ω p))
        · have hr : IsPivot (sem n (Gen.ω p) * s) p := by
            refine isPivot_mul hp hgidx fun he => ?_
            have := num_eq_ev hur (by rw [hcolr]; exact he) p
            rw [if_pos rfl, Function.update_self] at this
            have h1 : ωz ^ (1 + uexp (u p)) = ωz ^ 0 := by
              rw [pow_add, pow_one, ωz_pow_uexp hc1', this, pow_zero]
            have := ωz_pow_inj h1
            omega
          have hsylr := syl_unit_eq_of hr hur hur1 hur0
          rw [Function.update_self] at hsylr
          refine sq_gen hr.ne_one hsylr (G' := 1) ?_ (AllBelow.one' (level_syl_lt hs))
          rw [hsyl, derivable_iff]
          simp only [map_mul, map_pow, cl_ω, one_mul]
          exact gω_pow_sub_succ p hm ⟨hm1', hm'⟩ hmm
      · have hjp' : j < p := lt_of_le_of_ne hjp (Ne.symm hpj)
        have hsyl := syl_unit_lt_of hp hu hcne' hc0' hjp'
        have hr : IsPivot (sem n (Gen.ω j) * s) p := by
          refine isPivot_mul hp hgidx fun he => ?_
          have := num_eq_ev hur (by rw [hcolr]; exact he) j
          rw [if_neg (Ne.symm hpj), Function.update_self] at this
          exact ωz_mul_ne_zero hcne' this
        have hsylr := syl_unit_lt_of hr hur hur1 hur0 hjp'
        rw [Function.update_self] at hsylr
        refine sq_gen hr.ne_one hsylr (G' := 1) ?_ (AllBelow.one' (level_syl_lt hs))
        rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_X, one_mul]
        rw [mul_assoc, e11 j p hjp', ← mul_assoc, gω_pow_sub_succ p hm ⟨hm1', hm'⟩ hmm]
    · -- Subcase 2.4: the pivot column is `ωᵐ e_c`, `c ≠ 0`
      have hjc : j < c := lt_of_le_of_ne (Fin.le_def.2 (by omega)) (Ne.symm hcj)
      have hjp' : j < p := lt_of_lt_of_le hjc hcp
      have hvj : col s p j = 0 := by
        have := hu j; rw [pow_zero, one_mul, hc0 j (Ne.symm hcj), map_zero] at this; exact this
      have hcol : col (sem n (Gen.ω j) * s) p = col s p := by
        rw [hcolr]; exact oneLevel_mulVec_of_zero _ _ hvj
      have hr : IsPivot (sem n (Gen.ω j) * s) p := by
        refine isPivot_mul hp hgidx ?_
        show oneLevel j QCert.ω *ᵥ col s p ≠ ev p
        rw [← hcolr, hcol]; exact hp.1
      have hsylr : syl (sem n (Gen.ω j) * s) = syl s := by rw [syl_eq hr, syl_eq hp, hcol]
      refine sq_gen hr.ne_one hsylr (G' := ω j) ?_ ?_
      · -- `ω_[0]` commutes with the syllable
        rw [derivable_iff]
        simp only [map_mul, cl_ω]
        rcases hcp.lt_or_eq with hcp' | hcp'
        · rw [syl_unit_lt_of hp hu hcne hc0 hcp']
          simp only [map_mul, map_pow, cl_ω, cl_X]
          have h1 : Commute (gω j) (gω p ^ (8 - uexp (u c))) :=
            (c_ωω (ne_of_lt hjp')).pow_right _
          have h2 : Commute (gω j) (gX c p hcp') :=
            c_ωX hcp' (ne_of_lt hjc) (ne_of_lt hjp')
          exact ((h1.mul_right h2).eq).symm
        · have hc1' : nrm0 (u p) = 1 := hcp' ▸ hc1
          have hc0' : ∀ a, a ≠ p → u a = 0 := hcp' ▸ hc0
          have hcne' : u p ≠ 0 := hcp' ▸ hcne
          rw [syl_unit_eq_of hp hu hcne' hc0']
          simp only [map_pow, cl_ω]
          exact ((c_ωω (ne_of_lt hjp')).pow_right _).eq.symm
      · apply allBelow_A hp (t_above hp hk)
        refine AllL.of ?_
        intro i hi
        simp only [gidx, List.mem_singleton] at hi
        rw [hi]; exact hjp'
  · -- `k > 0`: Subcases 2.1 and 2.2
    obtain ⟨α, β, hf, hβp⟩ := odd_data' hp hu hk rfl
    have hsyl := syl_H_of hp hu hk hf
    have hf' : FirstTwo (Function.update u j (ωz * u j)) α β :=
      hf.of_iff (isOdd_update_ωz u j)
    have hr : IsPivot (sem n (Gen.ω j) * s) p := by
      refine isPivot_mul hp hgidx ?_
      show oneLevel j QCert.ω *ᵥ col s p ≠ ev p
      rw [← hcolr]; exact ne_ev_of_hasNum hur hk ⟨α, hf'.2.1⟩ p
    have hsylr := syl_H_of' hr hur hk hf' hf.1
    have hαp : α ≤ p := le_trans hf.1.le hβp
    have hβj : β ≠ j := ne_of_gt (lt_of_le_of_lt (Fin.le_def.2 (by omega)) hf.1)
    obtain ⟨ht1, ht2⟩ := t_below hp hk
    by_cases hαj : α = j
    · -- Subcase 2.1: the first odd entry is the entry `0`
      subst j
      rw [Function.update_self, Function.update_of_ne hβj,
        zexp_ωz_mul hf.2.1] at hsylr
      have hz := zexp_lt (u α) (u β)
      by_cases hz0 : zexp (u α) (u β) = 0
      · rw [hz0] at hsylr hsyl
        refine sq_gen hr.ne_one hsylr (G' := ω α ^ 4 * ω β ^ 4 * X α β hf.1) ?_ ?_
        · rw [hsyl, derivable_iff]
          simp only [map_mul, map_pow, cl_ω, cl_X, cl_H, pow_zero, mul_one]
          rw [mul_assoc (gH α β hf.1), ← pow_succ]
          exact eH4 α β hf.1
        · apply allBelow_B hp ht1 ht2
          refine ((AllL.of ?_).pow 4 |>.mul ((AllL.of ?_).pow 4)).mul (AllL.of ?_)
          · exact ⟨trivial, by simp [gidx, hαp]⟩
          · exact ⟨trivial, by simp [gidx, hβp]⟩
          · exact ⟨trivial, by simp [gidx, hαp, hβp]⟩
      · -- "almost retrograde": `N' ω_[0] = N`
        refine sq_gen hr.ne_one hsylr (G' := 1) ?_ (AllBelow.one' (level_syl_lt hs))
        rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_H, one_mul]
        rw [mul_assoc (gH α β _), ← pow_succ]
        congr 2
        omega
    · -- Subcase 2.2: the entry `0` is even
      have hαj' : α ≠ j := hαj
      rw [Function.update_of_ne hαj', Function.update_of_ne hβj, ← hsyl] at hsylr
      refine sq_gen hr.ne_one hsylr (G' := ω j) ?_ ?_
      · rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_H]
        have h1 : Commute (gω j) (gH α β hf.1) := c_ωH hf.1 (Ne.symm hαj') (Ne.symm hβj)
        have h2 : Commute (gω j) (gω α ^ zexp (u α) (u β)) :=
          (c_ωω (Ne.symm hαj')).pow_right _
        exact ((h1.mul_right h2).eq).symm
      · apply allBelow_B hp ht1 ht2
        exact AllL.of ⟨trivial, by simp [gidx, hjp]⟩

end

end QCert.Greylyn
