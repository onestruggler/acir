/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the edges out of the identity

The base case of the proof of Lemma 32: "an easy case distinction shows
that the claim holds for all basic generators".  It holds for every
generator `G`: the normal word of the state `G` is its one syllable, which
undoes `G` by one of (1)–(3):

* `ω_[j]`: the pivot column `j` is `ω e_j`, and the syllable is `ω⁷_[j]`;
* `X_[j,k]`: the pivot column `k` is `e_j = ω⁸ e_j`, and the syllable is
  `ω⁰_[k] X_[j,k]`;
* `H_[j,k]`: the pivot column `k` is `(e_j - e_k)/√2`, of least δ-exponent
  `2` with numerator `ω λ (e_j - e_k)`; `ω λ = 1 + ω + ω² ≡ ω³ ≡ -ω λ
  (mod δ³)`, so the syllable is `H_[j,k] ω⁰_[j]`.
-/
import QCert.Greylyn.LevelBound

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem ev_self (q : Fin n) : ev q q = 1 := by simp [ev]

theorem col_sem (x : Gen n) (q : Fin n) : col (sem n x) q = mat x *ᵥ ev q :=
  (mulVec_ev _ q).symm

/-- An edge `I → x` whose state has the syllable `u` with `u x ≈ ε`. -/
theorem step_one {x : Gen n} {u : Word (Gen n)} (hpiv : sem n x ≠ 1) (hsyl : syl (sem n x) = u)
    (hrel : Derivable (Rel n) (u * FreeMonoid.of x) 1) : Step (1 : St n) x := by
  have hback : ⟪u⟫ * sem n x = 1 := by
    have := derivable_sound (fun _ _ h => sound h) hrel
    rwa [map_mul, FreeMonoid.lift_eval_of, map_one] at this
  unfold Step
  rw [mul_one, nw_of_ne hpiv, hsyl, hback, nw_one, one_mul]
  exact hrel

/-! ### `ω_[j]` -/

/-- The numerator `ω e_j` of the column `j` of `ω_[j]`. -/
def wω (j : Fin n) : Fin n → ZOmega := fun a => if a = j then ωz else 0

theorem wω_self (j : Fin n) : wω j j = ωz := if_pos rfl
theorem wω_ne {j a : Fin n} (h : a ≠ j) : wω j a = 0 := if_neg h

theorem hasNum_ωcol (j : Fin n) : HasNum (col (sem n (Gen.ω j)) j) 0 (wω j) := by
  intro a
  rw [col_sem, pow_zero, one_mul]
  simp only [mat]
  rw [oneLevel_mulVec]
  by_cases haj : a = j
  · rw [haj, Function.update_self, wω_self, ev_self, mul_one, toC_ωz]
  · rw [Function.update_of_ne haj, wω_ne haj, ev_apply_ne haj, map_zero]

theorem isPivot_ω (j : Fin n) : IsPivot (sem n (Gen.ω j)) j := by
  refine ⟨fun he => ?_, fun q hq => ?_⟩
  · have h1 := hasNum_ωcol j j
    rw [he, ev_self, pow_zero, one_mul, wω_self, ← map_one toC] at h1
    exact absurd (toC_injective h1) (by decide)
  · rw [col_sem]
    simp only [mat]
    rw [oneLevel_mulVec_of_zero _ _ (ev_apply_ne (ne_of_lt hq))]

theorem syl_ω (j : Fin n) : syl (sem n (Gen.ω j)) = ω j ^ 7 := by
  have hu : uexp ωz = 1 := by decide
  rw [syl_eq (isPivot_ω j), sylCol_unit_eq (hasNum_ωcol j) (by rw [wω_self]; decide)
    (fun a ha => wω_ne ha), wω_self, hu]

/-! ### `X_[j,k]` -/

/-- The numerator `e_j` of the column `k` of `X_[j,k]`. -/
def wX (j : Fin n) : Fin n → ZOmega := fun a => if a = j then 1 else 0

theorem wX_self (j : Fin n) : wX j j = 1 := if_pos rfl
theorem wX_ne {j a : Fin n} (h : a ≠ j) : wX j a = 0 := if_neg h

theorem hasNum_Xcol {j k : Fin n} (h : j < k) :
    HasNum (col (sem n (Gen.X j k h)) k) 0 (wX j) := by
  intro a
  rw [col_sem, pow_zero, one_mul]
  simp only [mat]
  rw [twoLevel_mulVec h.ne]
  by_cases hak : a = k
  · rw [hak, Function.update_self, wX_ne h.ne', ev_apply_ne h.ne, ev_self, map_zero]
    simp [Xmat]
  · rw [Function.update_of_ne hak]
    by_cases haj : a = j
    · rw [haj, Function.update_self, wX_self, ev_apply_ne h.ne, ev_self, map_one]
      simp [Xmat]
    · rw [Function.update_of_ne haj, wX_ne haj, ev_apply_ne hak, map_zero]

theorem isPivot_X {j k : Fin n} (h : j < k) : IsPivot (sem n (Gen.X j k h)) k := by
  refine ⟨fun he => ?_, fun q hq => ?_⟩
  · have h1 := hasNum_Xcol h k
    rw [he, ev_self, pow_zero, one_mul, wX_ne h.ne', map_zero] at h1
    exact one_ne_zero h1
  · rw [col_sem]
    simp only [mat]
    rw [twoLevel_mulVec_of_zero h.ne _ (ev_apply_ne (ne_of_lt (h.trans hq)))
      (ev_apply_ne (ne_of_lt hq))]

theorem syl_X {j k : Fin n} (h : j < k) : syl (sem n (Gen.X j k h)) = ω k ^ 0 * X j k h := by
  have hu : uexp 1 = 8 := by decide
  rw [syl_eq (isPivot_X h), sylCol_unit_lt (hasNum_Xcol h) (by rw [wX_self]; decide)
    (fun a ha => wX_ne ha) h, wX_self, hu]

/-! ### `H_[j,k]` -/

/-- The numerator `ω λ (e_j - e_k)` of the column `k` of `H_[j,k]` at the
δ-exponent `2`. -/
def wH (j k : Fin n) : Fin n → ZOmega := fun a => if a = j then ηz else if a = k then -ηz else 0

theorem wH_j (j k : Fin n) : wH j k j = ηz := if_pos rfl
theorem wH_k {j k : Fin n} (h : k ≠ j) : wH j k k = -ηz := by
  unfold wH; rw [if_neg h, if_pos rfl]
theorem wH_ne {j k a : Fin n} (haj : a ≠ j) (hak : a ≠ k) : wH j k a = 0 := by
  unfold wH; rw [if_neg haj, if_neg hak]

theorem hasNum_Hcol {j k : Fin n} (h : j < k) :
    HasNum (col (sem n (Gen.H j k h)) k) 2 (wH j k) := by
  intro a
  rw [col_sem]
  simp only [mat]
  rw [twoLevel_mulVec h.ne]
  by_cases hak : a = k
  · rw [hak, Function.update_self, wH_k h.ne', ev_apply_ne h.ne, ev_self, Hmat_10, Hmat_11,
      map_neg, ← δ_sq_mul_invSqrt2]
    ring
  · rw [Function.update_of_ne hak]
    by_cases haj : a = j
    · rw [haj, Function.update_self, wH_j, ev_apply_ne h.ne, ev_self, Hmat_00, Hmat_01,
        ← δ_sq_mul_invSqrt2]
      ring
    · rw [Function.update_of_ne haj, wH_ne haj hak, ev_apply_ne hak, map_zero, mul_zero]

theorem isPivot_H {j k : Fin n} (h : j < k) : IsPivot (sem n (Gen.H j k h)) k := by
  refine ⟨fun he => ?_, fun q hq => ?_⟩
  · have h1 := hasNum_Hcol h j
    rw [he, ev_apply_ne h.ne, mul_zero, wH_j, ← map_zero toC] at h1
    exact absurd (toC_injective h1) (by decide)
  · rw [col_sem]
    simp only [mat]
    rw [twoLevel_mulVec_of_zero h.ne _ (ev_apply_ne (ne_of_lt (h.trans hq)))
      (ev_apply_ne (ne_of_lt hq))]

theorem syl_H {j k : Fin n} (h : j < k) : syl (sem n (Gen.H j k h)) = H j k h * ω j ^ 0 := by
  have hodd : IsOdd ηz := by decide
  have hodd' : IsOdd (-ηz) := by decide
  have hz : zexp ηz (-ηz) = 0 := by decide
  have hw := hasNum_Hcol h
  have hl : lde (col (sem n (Gen.H j k h)) k) = 2 :=
    lde_eq hw (Or.inr ⟨j, by rw [wH_j]; exact hodd⟩)
  have hf : FirstTwo (wH j k) j k := by
    refine ⟨h, by rw [wH_j]; exact hodd, by rw [wH_k h.ne']; exact hodd', fun a ha => ?_,
      fun a ha ha' => ?_⟩
    · rw [wH_ne ha.ne (ha.trans h).ne]; exact not_isOdd_zero
    · rw [wH_ne ha.ne' ha'.ne]; exact not_isOdd_zero
  have hz' : zexp (wH j k j) (wH j k k) = 0 := by rw [wH_j, wH_k h.ne']; exact hz
  rw [syl_eq (isPivot_H h), sylCol_H hw (by norm_num) hl hf, hz']

/-! ### The base case -/

/-- The edges out of `I` (proof of Lemma 32, base case), for every
generator. -/
theorem step_one_all (x : Gen n) : Step (1 : St n) x := by
  cases x with
  | X j k h =>
    exact step_one (isPivot_X h).ne_one (syl_X h)
      (by simpa [pow_two] using Derivable.of (Rel.r3 j k h))
  | H j k h =>
    exact step_one (isPivot_H h).ne_one (syl_H h)
      (by simpa [pow_two] using Derivable.of (Rel.r2 j k h))
  | ω j =>
    exact step_one (isPivot_ω j).ne_one (syl_ω j)
      (by simpa [← pow_succ] using Derivable.of (Rel.r1 j))

end

end QCert.Greylyn
