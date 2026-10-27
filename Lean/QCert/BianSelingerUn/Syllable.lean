/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: syllables, termination and normal words

Step 3 of Algorithm 2.14 (the syllable of a state), Theorem 2.16 (applying
the syllable lowers the level, so the algorithm terminates), and the normal
words of §3.2: `nw s` is the concatenation of the syllables of `s`, `S s`,
`S S s`, … down to `I`, with `⟦nw s⟧ s = I`.
-/
import QCert.BianSelingerUn.Algorithm

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

/-! ### Matrices of words -/

/-- `K† = K⁷ = ((1+i)/2) [[1, 1], [1, -1]]`. -/
def Kdmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + I) / 2, (1 + I) / 2; (1 + I) / 2, -((1 + I) / 2)]

/-- `(1 + i)/2 ∈ ℚ(ω)`. -/
def qcd : QOmega := ⟨1 / 2, 0, 1 / 2, 0⟩

theorem qK_pow_seven : qK ^ 7 = !![qcd, qcd; qcd, -qcd] := by decide +kernel

theorem Kmat_pow_seven : Kmat ^ 7 = Kdmat := by
  have h : QOmega.toC qcd = (1 + I) / 2 := by
    simp only [QOmega.toC, Quartic.lift_apply, qcd, ω_sq]; push_cast; ring
  rw [← qK_map, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply, qK_pow_seven]
  ext a b; fin_cases a <;> fin_cases b <;> simp [Kdmat, h, -Quartic.neg_def]

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
@[simp] theorem matOf_K (j k : Fin n) (h : j < k) : matOf (K j k h) = twoLevel j k Kmat := by
  simp [mat]
@[simp] theorem matOf_i (j : Fin n) : matOf (i j) = oneLevel j I := by simp [mat]

theorem matOf_Kd (j k : Fin n) (h : j < k) : matOf (K j k h ^ 7) = twoLevel j k Kdmat := by
  rw [map_pow, matOf_K, twoLevel_pow h.ne, Kmat_pow_seven]

theorem matOf_ipow (j : Fin n) (e : ℕ) : matOf (i j ^ e) = oneLevel j (I ^ e) := by
  rw [map_pow, matOf_i, oneLevel_pow]

theorem matOf_mul_mulVec (u w : Word (Gen n)) (v : Fin n → ℂ) :
    matOf (u * w) *ᵥ v = matOf u *ᵥ (matOf w *ᵥ v) := by
  rw [map_mul, mulVec_mulVec]

/-! ### Actions on numerators -/

theorem I_eq : I = ((iz : GaussianInt) : ℂ) := toComplex_iz.symm

theorem hasNum_oneLevel {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    (a : Fin n) (e : ℕ) :
    HasNum (oneLevel a (I ^ e) *ᵥ v) k (Function.update w a (iz ^ e * w a)) := by
  intro j
  rw [oneLevel_mulVec]
  by_cases hj : j = a
  · subst hj
    simp only [Function.update_self]
    rw [← mul_assoc, mul_comm (γ ^ k), mul_assoc, h j, GaussianInt.toComplex_mul, map_pow, I_eq]
  · simp only [Function.update_of_ne hj]; exact h j

theorem hasNum_X {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Xmat *ᵥ v) k (Function.update (Function.update w a (w b)) b (w a)) := by
  intro j
  rw [twoLevel_mulVec hab]
  by_cases hjb : j = b
  · subst hjb; simp [Xmat, h a]
  by_cases hja : j = a
  · subst hja; simp [Function.update_of_ne hjb, Xmat, h b]
  · simp [Function.update_of_ne hjb, Function.update_of_ne hja, h j]

theorem γ_mul_inv : γ * (1 + I)⁻¹ = 1 := mul_inv_cancel₀ γ_ne_zero

theorem γ_mul_half : γ * ((1 + I) / 2) = I := by
  rw [γ]; ring_nf; rw [I_sq]; ring

theorem hasNum_K {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Kmat *ᵥ v) (k + 1)
      (Function.update (Function.update (fun c => γz * w c) a (w a + w b)) b (w a - w b)) := by
  intro j
  rw [twoLevel_mulVec hab]
  have e1 : ∀ x y : ℂ, γ ^ (k + 1) * ((1 + I)⁻¹ * x + (1 + I)⁻¹ * y) = γ ^ k * x + γ ^ k * y := by
    intro x y; rw [pow_succ]; linear_combination (γ ^ k * (x + y)) * γ_mul_inv
  have e2 : ∀ x y : ℂ, γ ^ (k + 1) * ((1 + I)⁻¹ * x + -(1 + I)⁻¹ * y) = γ ^ k * x - γ ^ k * y := by
    intro x y; rw [pow_succ]; linear_combination (γ ^ k * (x - y)) * γ_mul_inv
  have hh : ∀ x, γ ^ k * v x = (w x : ℂ) := h
  rcases eq_or_ne j b with rfl | hjb
  · simp only [Function.update_self]
    rw [show Kmat 1 0 = (1 + I)⁻¹ from rfl, show Kmat 1 1 = -(1 + I)⁻¹ from rfl, e2, hh, hh,
      GaussianInt.toComplex_sub]
  rcases eq_or_ne j a with rfl | hja
  · rw [Function.update_of_ne hjb, Function.update_self, Function.update_of_ne hjb,
      Function.update_self, show Kmat 0 0 = (1 + I)⁻¹ from rfl,
      show Kmat 0 1 = (1 + I)⁻¹ from rfl, e1, hh, hh, GaussianInt.toComplex_add]
  · rw [Function.update_of_ne hjb, Function.update_of_ne hja, Function.update_of_ne hjb,
      Function.update_of_ne hja, GaussianInt.toComplex_mul, toComplex_γz, pow_succ', mul_assoc, hh]

theorem hasNum_Kd {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Kdmat *ᵥ v) (k + 1)
      (Function.update (Function.update (fun c => γz * w c) a (iz * (w a + w b))) b
        (iz * (w a - w b))) := by
  intro j
  rw [twoLevel_mulVec hab]
  have e1 : ∀ x y : ℂ, γ ^ (k + 1) * ((1 + I) / 2 * x + (1 + I) / 2 * y) =
      I * (γ ^ k * x + γ ^ k * y) := by
    intro x y; rw [pow_succ]; linear_combination (γ ^ k * (x + y)) * γ_mul_half
  have e2 : ∀ x y : ℂ, γ ^ (k + 1) * ((1 + I) / 2 * x + -((1 + I) / 2) * y) =
      I * (γ ^ k * x - γ ^ k * y) := by
    intro x y; rw [pow_succ]; linear_combination (γ ^ k * (x - y)) * γ_mul_half
  have hh : ∀ x, γ ^ k * v x = (w x : ℂ) := h
  rcases eq_or_ne j b with rfl | hjb
  · simp only [Function.update_self]
    rw [show Kdmat 1 0 = (1 + I) / 2 from rfl, show Kdmat 1 1 = -((1 + I) / 2) from rfl, e2, hh, hh,
      GaussianInt.toComplex_mul, GaussianInt.toComplex_sub, toComplex_iz]
  rcases eq_or_ne j a with rfl | hja
  · rw [Function.update_of_ne hjb, Function.update_self, Function.update_of_ne hjb,
      Function.update_self, show Kdmat 0 0 = (1 + I) / 2 from rfl,
      show Kdmat 0 1 = (1 + I) / 2 from rfl, e1, hh, hh, GaussianInt.toComplex_mul,
      GaussianInt.toComplex_add, toComplex_iz]
  · rw [Function.update_of_ne hjb, Function.update_of_ne hja, Function.update_of_ne hjb,
      Function.update_of_ne hja, GaussianInt.toComplex_mul, toComplex_γz, pow_succ', mul_assoc, hh]

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

/-! ### Parity facts -/

theorem γz_sq_dvd_iff (g : GaussianInt) : γz ^ 2 ∣ g ↔ g.re % 2 = 0 ∧ g.im % 2 = 0 := by
  have hγ : γz ^ 2 = ⟨0, 2⟩ := by decide
  rw [hγ]
  constructor
  · rintro ⟨c, rfl⟩; simp
  · rintro ⟨h1, h2⟩
    refine ⟨⟨g.im / 2, -(g.re / 2)⟩, ?_⟩
    ext <;> simp <;> omega

/-- `wⱼ ≡ i^q w_ℓ (mod γ²)` (Lemma 2.10): `q = 0` when the two odd numbers
have the same parity pattern, `q = 1` otherwise. -/
def qexp (a b : GaussianInt) : ℕ := if a.re % 2 = b.re % 2 then 0 else 1

theorem qexp_le (a b : GaussianInt) : qexp a b ≤ 1 := by unfold qexp; split_ifs <;> omega

/-- Lemma 2.10: for odd `a, b`, `γ²` divides `a ± i^q b`. -/
theorem γz_sq_dvd_add_sub {a b : GaussianInt} (ha : GOdd a) (hb : GOdd b) :
    γz ^ 2 ∣ a + iz ^ qexp a b * b ∧ γz ^ 2 ∣ a - iz ^ qexp a b * b := by
  unfold GOdd at ha hb
  rw [γz_sq_dvd_iff, γz_sq_dvd_iff]
  unfold qexp
  split_ifs with h
  · simp; omega
  · simp [iz]; omega

/-! ### First two odd entries -/

/-- `j < ℓ` are the first two odd entries of `w`. -/
def FirstTwo (w : Fin n → GaussianInt) (j l : Fin n) : Prop :=
  j < l ∧ GOdd (w j) ∧ GOdd (w l) ∧ (∀ a, a < j → ¬ GOdd (w a)) ∧
    (∀ a, j < a → a < l → ¬ GOdd (w a))

theorem FirstTwo.unique {w : Fin n → GaussianInt} {j l j' l' : Fin n} (h : FirstTwo w j l)
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

theorem exists_firstTwo {w : Fin n → GaussianInt} (h : 2 ≤ (oddSet w).card) :
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

theorem K_congr {a b a' b' : Fin n} (h : a < b) (h' : a' < b') (ea : a = a') (eb : b = b') :
    K a b h = K a' b' h' := by subst ea; subst eb; rfl

open Classical in
/-- The syllable of Algorithm 2.14 for the pivot column `v` at index `p`. -/
def sylCol (p : Fin n) (v : Fin n → ℂ) : Word (Gen n) :=
  if lde v = 0 then
    if h : ∃ c, num v c ≠ 0 then
      if hcp : h.choose < p then X h.choose p hcp * i h.choose ^ expo (num v h.choose)
      else i p ^ expo (num v p)
    else 1
  else if h : ∃ j l, FirstTwo (num v) j l then
    K h.choose h.choose_spec.choose h.choose_spec.choose_spec.1 ^ 7 *
      i h.choose_spec.choose ^ qexp (num v h.choose) (num v h.choose_spec.choose)
  else 1

open Classical in
/-- The syllable of a state (step 3 of Algorithm 2.14). -/
def syl (s : St n) : Word (Gen n) :=
  if h : ∃ p, IsPivot s p then sylCol h.choose (col s h.choose) else 1

theorem syl_eq {s : St n} {p : Fin n} (h : IsPivot s p) : syl s = sylCol p (col s p) := by
  have h' : ∃ p, IsPivot s p := ⟨p, h⟩
  rw [syl, dif_pos h', h'.choose_spec.unique h]

theorem syl_one : syl (1 : St n) = 1 := by
  rw [syl, dif_neg]; rintro ⟨p, hp⟩; exact hp.ne_one rfl

/-- The syllable for a unit pivot column `i^{-e} e_c` with `c < p`. -/
theorem sylCol_unit_lt {p c : Fin n} {v : Fin n → ℂ} {w : Fin n → GaussianInt}
    (hv : HasNum v 0 w) (hc : w c ≠ 0) (hz : ∀ a, a ≠ c → w a = 0) (hcp : c < p) :
    sylCol p v = X c p hcp * i c ^ expo (w c) := by
  have hl : lde v = 0 := lde_eq hv (Or.inl rfl)
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ c, num v c ≠ 0 := ⟨c, by rw [hnum]; exact hc⟩
  have hch : hex.choose = c := by
    by_contra hne; apply hex.choose_spec; rw [congrFun hnum]; exact hz _ hne
  rw [sylCol, if_pos hl, dif_pos hex, dif_pos (hch ▸ hcp), X_congr _ hcp hch rfl, hch, hnum]

/-- The syllable for a unit pivot column `i^{-e} e_p`. -/
theorem sylCol_unit_eq {p : Fin n} {v : Fin n → ℂ} {w : Fin n → GaussianInt}
    (hv : HasNum v 0 w) (hc : w p ≠ 0) (hz : ∀ a, a ≠ p → w a = 0) :
    sylCol p v = i p ^ expo (w p) := by
  have hl : lde v = 0 := lde_eq hv (Or.inl rfl)
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ c, num v c ≠ 0 := ⟨p, by rw [hnum]; exact hc⟩
  have hch : hex.choose = p := by
    by_contra hne; apply hex.choose_spec; rw [congrFun hnum]; exact hz _ hne
  rw [sylCol, if_pos hl, dif_pos hex, dif_neg (by rw [hch]; exact lt_irrefl p), hnum]

/-- The syllable `K†_[j,ℓ] i_[ℓ]^q` at a positive exponent. -/
theorem sylCol_K {p j l : Fin n} {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt}
    (hv : HasNum v k w) (hk : 0 < k) (hl : lde v = k) (hf : FirstTwo w j l) :
    sylCol p v = K j l hf.1 ^ 7 * i l ^ qexp (w j) (w l) := by
  have hnum : num v = w := num_eq (hl ▸ hv)
  have hex : ∃ j l, FirstTwo (num v) j l := ⟨j, l, by rw [hnum]; exact hf⟩
  rw [sylCol, if_neg (by omega), dif_pos hex]
  have key : ∀ x y, FirstTwo (num v) x y → FirstTwo w x y := by rw [hnum]; exact fun _ _ h => h
  have hf' : FirstTwo w hex.choose hex.choose_spec.choose := key _ _ hex.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := hf'.unique hf
  have hq : qexp (num v hex.choose) (num v hex.choose_spec.choose) = qexp (w j) (w l) := by
    rw [e2, e1, congrFun hnum, congrFun hnum]
  rw [hq, K_congr _ hf.1 e1 e2, e2]

end

end QCert.BianSelingerUn
