/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: syllables

Step 2 of Algorithm 16 and the syllables of Definition 17.  For the pivot
column `v = Meⱼ` of a state, with least δ-exponent `k` and numerator
`u = δᵏ v`:

* `k = 0`: by Lemma 14, `v = ωᵐ e_ℓ` with `m ∈ {1, …, 8}` and `ℓ ≤ j`; the
  syllable is `ω^{8-m}_[j] X_[ℓ,j]`, or `ω^{8-m}_[j]` if `ℓ = j`;
* `k > 0`: `ι < ℓ` are the first two odd entries of `u`, `u_ι ≡ ωᵐ` and
  `u_ℓ ≡ ω^q (mod δ³)` (Lemma 11), `z = (q - m) mod 4`, and the syllable is
  `H_[ι,ℓ] ω^z_[ι]`.

A word denotes the product of its letters in the order written, so the
syllable `ω^{8-m}_[j] X_[ℓ,j]` applies `X_[ℓ,j]` first.  Also: the actions
of the generators on numerators (`hasNum_ω`, `hasNum_X`, and Lemma 12 as
`hasNum_H_red`: `H` takes two entries `≡ 0 (mod δ³)` in sum and difference
to entries `≡ 0 (mod δ)` at the same exponent).
-/
import QCert.Greylyn.Algorithm

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

/-! ### Matrices of words -/

theorem twoLevel_pow {a b : Fin n} (hab : a ≠ b) (U : Matrix (Fin 2) (Fin 2) ℂ) (e : ℕ) :
    twoLevel a b U ^ e = twoLevel a b (U ^ e) := by
  have := map_pow (levelHom (R := ℂ) (injective_pair hab)) U e
  simpa [twoLevel] using this.symm

theorem oneLevel_pow (a : Fin n) (z : ℂ) (e : ℕ) : oneLevel a z ^ e = oneLevel a (z ^ e) := by
  have hz : ∀ e : ℕ, (!![z] : Matrix (Fin 1) (Fin 1) ℂ) ^ e = !![z ^ e] := by
    intro e
    induction e with
    | zero => ext a b; fin_cases a; fin_cases b; simp
    | succ e ih =>
      rw [pow_succ, ih]; ext a b; fin_cases a; fin_cases b; simp [mul_apply, pow_succ]
  have := map_pow (levelHom (R := ℂ) (injective_single a)) !![z] e
  simpa [oneLevel, hz] using this.symm

@[simp] theorem matOf_X (j k : Fin n) (h : j < k) : matOf (X j k h) = twoLevel j k Xmat := by
  simp [mat]
@[simp] theorem matOf_H (j k : Fin n) (h : j < k) : matOf (H j k h) = twoLevel j k Hmat := by
  simp [mat]
@[simp] theorem matOf_ω (j : Fin n) : matOf (ω j) = oneLevel j QCert.ω := by simp [mat]

theorem matOf_ωpow (j : Fin n) (e : ℕ) : matOf (ω j ^ e) = oneLevel j (QCert.ω ^ e) := by
  rw [map_pow, matOf_ω, oneLevel_pow]

theorem matOf_mul_mulVec (u w : Word (Gen n)) (v : Fin n → ℂ) :
    matOf (u * w) *ᵥ v = matOf u *ᵥ (matOf w *ᵥ v) := by
  rw [map_mul, mulVec_mulVec]

/-! ### Actions on numerators -/

theorem hasNum_ω {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w)
    (a : Fin n) (e : ℕ) :
    HasNum (oneLevel a (QCert.ω ^ e) *ᵥ v) k (Function.update w a (ωz ^ e * w a)) := by
  intro j
  rw [oneLevel_mulVec]
  by_cases hj : j = a
  · subst hj
    simp only [Function.update_self]
    rw [← mul_assoc, mul_comm (δ ^ k), mul_assoc, h j, map_mul, map_pow, toC_ωz]
  · simp only [Function.update_of_ne hj]; exact h j

theorem hasNum_X {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Xmat *ᵥ v) k (Function.update (Function.update w a (w b)) b (w a)) := by
  intro j
  rw [twoLevel_mulVec hab]
  by_cases hjb : j = b
  · subst hjb; simp [Xmat, h a]
  by_cases hja : j = a
  · subst hja; simp [Function.update_of_ne hjb, Xmat, h b]
  · simp [Function.update_of_ne hjb, Function.update_of_ne hja, h j]

theorem Hmat_00 : Hmat 0 0 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := rfl
theorem Hmat_01 : Hmat 0 1 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := rfl
theorem Hmat_10 : Hmat 1 0 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := rfl
theorem Hmat_11 : Hmat 1 1 = -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := rfl

/-- Lemma 12, on numerators: if `wₐ ± w_b ≡ 0 (mod δ³)`, then `H_[a,b]`
keeps the δ-exponent and makes the entries `a`, `b` divisible by `δ`
(`(wₐ ± w_b)/√2 = ω λ (wₐ ± w_b)/δ²`). -/
theorem hasNum_H_red {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) {d1 d2 : ZOmega} (h1 : w a + w b = δz ^ 3 * d1)
    (h2 : w a - w b = δz ^ 3 * d2) :
    HasNum (twoLevel a b Hmat *ᵥ v) k
      (Function.update (Function.update w a (ηz * δz * d1)) b (ηz * δz * d2)) := by
  intro j
  have hη : δ ^ 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = toC ηz := δ_sq_mul_invSqrt2
  have e1 : toC (w a) + toC (w b) = δ ^ 3 * toC d1 := by
    rw [← map_add, h1, map_mul, map_pow, toC_δz']
  have e2 : toC (w a) - toC (w b) = δ ^ 3 * toC d2 := by
    rw [← map_sub, h2, map_mul, map_pow, toC_δz']
  have ha := h a
  have hb := h b
  rw [twoLevel_mulVec hab]
  simp only [Function.update_apply]
  split_ifs with hjb hja
  · rw [Hmat_10, Hmat_11, map_mul, map_mul, ← hη, toC_δz']
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ha - ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hb +
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * e2
  · rw [Hmat_00, Hmat_01, map_mul, map_mul, ← hη, toC_δz']
    linear_combination ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ha + ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hb +
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * e1
  · exact h j

/-- A two-level matrix fixes a vector vanishing at its two indices. -/
theorem twoLevel_mulVec_of_zero {a b : Fin n} (hab : a ≠ b) (U : Matrix (Fin 2) (Fin 2) ℂ)
    {v : Fin n → ℂ} (ha : v a = 0) (hb : v b = 0) : twoLevel a b U *ᵥ v = v := by
  rw [twoLevel_mulVec hab, ha, hb]
  funext x
  simp only [mul_zero, add_zero, Function.update_apply]
  split_ifs <;> simp_all

theorem oneLevel_mulVec_of_zero (a : Fin n) (z : ℂ) {v : Fin n → ℂ} (ha : v a = 0) :
    oneLevel a z *ᵥ v = v := by
  rw [oneLevel_mulVec, ha]
  funext x
  simp only [mul_zero, Function.update_apply]
  split_ifs <;> simp_all

/-! ### First two odd entries -/

/-- `j < ℓ` are the first two odd entries of `w`. -/
def FirstTwo (w : Fin n → ZOmega) (j l : Fin n) : Prop :=
  j < l ∧ IsOdd (w j) ∧ IsOdd (w l) ∧ (∀ a, a < j → ¬ IsOdd (w a)) ∧
    (∀ a, j < a → a < l → ¬ IsOdd (w a))

theorem FirstTwo.unique {w : Fin n → ZOmega} {j l j' l' : Fin n} (h : FirstTwo w j l)
    (h' : FirstTwo w j' l') : j = j' ∧ l = l' := by
  obtain ⟨hjl, hj, hl, h1, h2⟩ := h
  obtain ⟨hjl', hj', hl', h1', h2'⟩ := h'
  have e1 : j = j' := by
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd hj (h1' j h)
    · exact h
    · exact absurd hj' (h1 j' h)
  subst e1
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy l l' with h | h | h
  · exact absurd hl (h2' l hjl h)
  · exact h
  · exact absurd hl' (h2 l' hjl' h)

theorem exists_firstTwo {w : Fin n → ZOmega} (h : 2 ≤ (oddSet w).card) :
    ∃ j l, FirstTwo w j l := by
  have hne : (oddSet w).Nonempty := Finset.card_pos.1 (by omega)
  let j := (oddSet w).min' hne
  have hj : j ∈ oddSet w := Finset.min'_mem _ _
  have hne' : ((oddSet w).erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj]; omega
  let l := ((oddSet w).erase j).min' hne'
  have hl : l ∈ (oddSet w).erase j := Finset.min'_mem _ _
  rw [Finset.mem_erase] at hl
  refine ⟨j, l, ?_, mem_oddSet.1 hj, mem_oddSet.1 hl.2, fun a ha hodd => ?_,
    fun a ha ha' hodd => ?_⟩
  · exact lt_of_le_of_ne (Finset.min'_le _ _ hl.2) (Ne.symm hl.1)
  · exact absurd (Finset.min'_le _ _ (mem_oddSet.2 hodd)) (not_le.2 ha)
  · exact absurd (Finset.min'_le _ _ (Finset.mem_erase.2 ⟨ne_of_gt ha, mem_oddSet.2 hodd⟩))
      (not_le.2 ha')

/-! ### The syllable -/

theorem X_congr {a b a' b' : Fin n} (h : a < b) (h' : a' < b') (ea : a = a') (eb : b = b') :
    X a b h = X a' b' h' := by subst ea; subst eb; rfl

theorem H_congr {a b a' b' : Fin n} (h : a < b) (h' : a' < b') (ea : a = a') (eb : b = b') :
    H a b h = H a' b' h' := by subst ea; subst eb; rfl

open Classical in
/-- The syllable of Algorithm 16 (step 2) for the pivot column `v` at index
`p`: `ω^{8-m}_[p] X_[ℓ,p]` (or `ω^{8-m}_[p]` if `ℓ = p`) for `v = ωᵐ e_ℓ`
(`k = 0`), and `H_[ι,ℓ] ω^z_[ι]` for the first two odd entries `ι < ℓ` of
the numerator (`k > 0`). -/
def sylCol (p : Fin n) (v : Fin n → ℂ) : Word (Gen n) :=
  if lde v = 0 then
    if h : ∃ c, num v c ≠ 0 then
      if hcp : h.choose < p then ω p ^ (8 - uexp (num v h.choose)) * X h.choose p hcp
      else ω p ^ (8 - uexp (num v p))
    else 1
  else if h : ∃ j l, FirstTwo (num v) j l then
    H h.choose h.choose_spec.choose h.choose_spec.choose_spec.1 *
      ω h.choose ^ zexp (num v h.choose) (num v h.choose_spec.choose)
  else 1

open Classical in
/-- The syllable of a state (Definition 17): the output of step 3 of
Algorithm 16. -/
def syl (s : St n) : Word (Gen n) :=
  if h : ∃ p, IsPivot s p then sylCol h.choose (col s h.choose) else 1

theorem syl_eq {s : St n} {p : Fin n} (h : IsPivot s p) : syl s = sylCol p (col s p) := by
  have h' : ∃ p, IsPivot s p := ⟨p, h⟩
  rw [syl, dif_pos h', h'.choose_spec.unique h]

theorem syl_one : syl (1 : St n) = 1 := by
  rw [syl, dif_neg]; rintro ⟨p, hp⟩; exact hp.ne_one rfl

/-- The syllable `ω^{8-m}_[p] X_[c,p]` for a unit pivot column `ωᵐ e_c`,
`c < p`. -/
theorem sylCol_unit_lt {p c : Fin n} {v : Fin n → ℂ} {w : Fin n → ZOmega}
    (hv : HasNum v 0 w) (hc : w c ≠ 0) (hz : ∀ a, a ≠ c → w a = 0) (hcp : c < p) :
    sylCol p v = ω p ^ (8 - uexp (w c)) * X c p hcp := by
  have hl : lde v = 0 := lde_eq hv (Or.inl rfl)
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ c, num v c ≠ 0 := ⟨c, by rw [hnum]; exact hc⟩
  have hch : hex.choose = c := by
    by_contra hne; apply hex.choose_spec; rw [congrFun hnum]; exact hz _ hne
  rw [sylCol, if_pos hl, dif_pos hex, dif_pos (hch ▸ hcp), X_congr _ hcp hch rfl, hch, hnum]

/-- The syllable `ω^{8-m}_[p]` for a unit pivot column `ωᵐ e_p`. -/
theorem sylCol_unit_eq {p : Fin n} {v : Fin n → ℂ} {w : Fin n → ZOmega}
    (hv : HasNum v 0 w) (hc : w p ≠ 0) (hz : ∀ a, a ≠ p → w a = 0) :
    sylCol p v = ω p ^ (8 - uexp (w p)) := by
  have hl : lde v = 0 := lde_eq hv (Or.inl rfl)
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ c, num v c ≠ 0 := ⟨p, by rw [hnum]; exact hc⟩
  have hch : hex.choose = p := by
    by_contra hne; apply hex.choose_spec; rw [congrFun hnum]; exact hz _ hne
  rw [sylCol, if_pos hl, dif_pos hex, dif_neg (by rw [hch]; exact lt_irrefl p), hnum]

/-- The syllable `H_[j,ℓ] ω^z_[j]` at a positive exponent. -/
theorem sylCol_H {p j l : Fin n} {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega}
    (hv : HasNum v k w) (hk : 0 < k) (hl : lde v = k) (hf : FirstTwo w j l) :
    sylCol p v = H j l hf.1 * ω j ^ zexp (w j) (w l) := by
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ j l, FirstTwo (num v) j l := ⟨j, l, by rw [hnum]; exact hf⟩
  rw [sylCol, if_neg (by omega), dif_pos hex]
  have key : ∀ x y, FirstTwo (num v) x y → FirstTwo w x y := by rw [hnum]; exact fun _ _ h => h
  have hf' : FirstTwo w hex.choose hex.choose_spec.choose := key _ _ hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := hf'.unique hf
  have hq : zexp (num v hex.choose) (num v hex.choose_spec.choose) = zexp (w j) (w l) := by
    rw [e2, e1, congrFun hnum, congrFun hnum]
  rw [hq, H_congr _ hf.1 e1 e2, e1]

end

end QCert.Greylyn
