/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the squares of the Main Lemma

The conclusion of Lemma 31 at a state `s` and a basic generator `x`
(`Square s x`): a state `q`, normal edges `x s ⇒ q` labelled `N'`, simple
edges `t → q` labelled `G'` (`t = N s`, `N` the syllable of `s`) all of
whose states have level below that of `s`, and `N' x ≈ G' N`.  Three ways
to close a square:

* `sq_triv`: the syllable of `s` is `x` itself (`t = r`, Subcase 1.1);
* `sq_retro`: the edge `s → x s` is retrograde (Definition 40): the normal
  edge out of `x s` is `N''` with `N'' x ≈ ε`;
* `sq_gen`: the normal edge out of `r = x s` is `N'` and `N' x ≈ G' N`.

The level condition on `G'` (`AllBelow`) is checked with two invariants
along words: letters with all indices below the pivot `p` keep the columns
from `p` on equal to the identity (`allBelow_A`, after a syllable of a
column with `k = 0`), and `X`- and `ω`-letters with indices at most `p`
keep the columns beyond `p` and the profile of column `p` (`allBelow_B`,
after a syllable of a column with `k > 0`): "the `ω` and `X` operations do
not change δ-exponents".  Also: the pivot column and the syllable of
`r = x s`, read off its numerator.
-/
import QCert.Greylyn.BaseCase
import QCert.Greylyn.Derived
import QCert.Greylyn.Residue

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-- The conclusion of Lemma 31 at `s` and `x`. -/
def Square (s : St n) (x : Gen n) : Prop :=
  ∃ (q : St n) (N' G' : Word (Gen n)), NormalPath (sem n x * s) N' q ∧
    ⟪G'⟫ * (⟪syl s⟫ * s) = q ∧ AllBelow (level s) (⟪syl s⟫ * s) G' ∧
    Derivable (Rel n) (N' * FreeMonoid.of x) (G' * syl s)

/-! ### Levels along words -/

theorem AllBelow.one' {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} (h : level t < L) : AllBelow L t 1 := by
  intro u v huv
  have h' : FreeMonoid.toList u ++ FreeMonoid.toList v = [] := by
    rw [← FreeMonoid.toList_mul, ← huv]; rfl
  have hv : v = 1 := FreeMonoid.toList.injective (List.append_eq_nil_iff.1 h').2
  subst hv
  simpa using h

theorem AllBelow.letter {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {y : Gen n} (h1 : level t < L)
    (h2 : level (sem n y * t) < L) : AllBelow L t (FreeMonoid.of y) := by
  intro u v huv
  rcases of_eq_mul_iff.1 huv with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · simpa using h2
  · simpa using h1

theorem AllBelow.mul {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {w1 w2 : Word (Gen n)}
    (h2 : AllBelow L t w2) (h1 : AllBelow L (⟪w2⟫ * t) w1) : AllBelow L t (w1 * w2) := by
  intro u v huv
  rcases mul_eq_mul_iff.1 huv with ⟨x, -, hx2⟩ | ⟨y, hy1, hy2⟩
  · exact h2 x v hx2
  · rw [hy2, map_mul, mul_assoc]; exact h1 u y hy1

/-- A property of states preserved by every letter of `w` and implying a
level below `L` bounds the levels along `w`. -/
theorem AllBelow.of_inv {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {w : Word (Gen n)} (P : St n → Prop)
    (hP : ∀ u, P u → level u < L)
    (hstep : ∀ y ∈ FreeMonoid.toList w, ∀ u, P u → P (sem n y * u)) (ht : P t) :
    AllBelow L t w := by
  intro u v huv
  apply hP
  have hv : ∀ y ∈ FreeMonoid.toList v, ∀ u, P u → P (sem n y * u) := fun y hy =>
    hstep y (by rw [huv, FreeMonoid.toList_mul]; exact List.mem_append_right _ hy)
  clear huv
  induction v using FreeMonoid.inductionOn' with
  | one => simpa using ht
  | mul_of y v ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc]
    exact hv y (by simp) _ (ih fun z hz => hv z (by simp [hz]))

/-- The indices of a generator. -/
def gidx : Gen n → List (Fin n)
  | .X a b _ => [a, b]
  | .H a b _ => [a, b]
  | .ω a => [a]

/-- `y` is an `X` or an `ω`. -/
def IsXω : Gen n → Prop
  | .X _ _ _ => True
  | .H _ _ _ => False
  | .ω _ => True

theorem mat_mulVec_ev_of_ne (y : Gen n) (q : Fin n) (h : ∀ i ∈ gidx y, i ≠ q) :
    mat y *ᵥ ev q = ev q := by
  cases y with
  | X a b hab =>
    simp only [gidx, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    simp only [mat]
    exact twoLevel_mulVec_of_zero hab.ne _ (ev_apply_ne h.1) (ev_apply_ne h.2)
  | H a b hab =>
    simp only [gidx, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    simp only [mat]
    exact twoLevel_mulVec_of_zero hab.ne _ (ev_apply_ne h.1) (ev_apply_ne h.2)
  | ω a =>
    simp only [gidx, List.mem_singleton, forall_eq] at h
    simp only [mat]
    exact oneLevel_mulVec_of_zero _ _ (ev_apply_ne h)

theorem twoLevel_X_mulVec {a b : Fin n} (hab : a ≠ b) (v : Fin n → ℂ) :
    twoLevel a b Xmat *ᵥ v = fun j => v ((Equiv.swap a b).symm j) := by
  rw [twoLevel_mulVec hab]
  funext j
  rw [Equiv.symm_swap]
  by_cases hjb : j = b
  · subst hjb; simp [Xmat, Equiv.swap_apply_right]
  by_cases hja : j = a
  · subst hja; simp [Function.update_of_ne hjb, Xmat, Equiv.swap_apply_left]
  · simp [Function.update_of_ne hjb, Function.update_of_ne hja,
      Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem hasNum_ω1 {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w) (a : Fin n) :
    HasNum (oneLevel a QCert.ω *ᵥ v) k (Function.update w a (ωz * w a)) := by
  have := hasNum_ω h a 1
  rwa [pow_one, pow_one] at this

theorem prof_oneLevel_ω (a : Fin n) {v : Fin n → ℂ} (hv : ∃ k w, HasNum v k w) :
    prof (oneLevel a QCert.ω *ᵥ v) = prof v := by
  have hw := num_spec hv
  have hw' := hasNum_ω1 hw a
  have hodd : ∀ j, IsOdd (Function.update (num v) a (ωz * num v a) j) ↔ IsOdd (num v j) := by
    intro j
    by_cases hj : j = a
    · subst hj; rw [Function.update_self, isOdd_ωz_mul]
    · rw [Function.update_of_ne hj]
  have hl : lde (oneLevel a QCert.ω *ᵥ v) = lde v := by
    apply lde_eq hw'
    rcases Nat.eq_zero_or_pos (lde v) with h0 | hpos
    · exact Or.inl h0
    · obtain ⟨j, hj⟩ := exists_odd hw hpos
      exact Or.inr ⟨j, (hodd j).2 hj⟩
  have hset : oddSet (Function.update (num v) a (ωz * num v a)) = oddSet (num v) := by
    ext j; simp only [mem_oddSet, hodd]
  rw [prof_eq hw' hl, prof, hset]

theorem prof_mat_Xω (y : Gen n) (hy : IsXω y) {v : Fin n → ℂ} (hv : ∃ k w, HasNum v k w) :
    prof (mat y *ᵥ v) = prof v := by
  cases y with
  | X a b hab =>
    simp only [mat]
    rw [twoLevel_X_mulVec hab.ne, prof_perm hv]
  | H a b hab => exact absurd hy (by simp [IsXω])
  | ω a => simp only [mat]; exact prof_oneLevel_ω a hv

/-- Invariant (A): letters with all indices below the pivot `p` of `s`
keep a state equal to the identity from column `p` on, hence below `s`. -/
theorem allBelow_A {s t : St n} {p : Fin n} (hs : IsPivot s p)
    (ht : ∀ q, p ≤ q → col t q = ev q) {w : Word (Gen n)}
    (hw : ∀ y ∈ FreeMonoid.toList w, ∀ i ∈ gidx y, i < p) : AllBelow (level s) t w := by
  apply AllBelow.of_inv (fun u => ∀ q, p ≤ q → col u q = ev q)
  · intro u hu
    exact level_lt_of_cols hs (fun q hq => hu q hq.le) (Or.inl (hu p le_rfl))
  · intro y hy u hu q hq
    rw [col_mul, hu q hq, sm_sem]
    exact mat_mulVec_ev_of_ne y q (fun i hi => ne_of_lt (lt_of_lt_of_le (hw y hy i hi) hq))
  · exact ht

/-- Invariant (B): `X`- and `ω`-letters with indices at most the pivot `p`
of `s` keep the columns beyond `p` and the profile of column `p`. -/
theorem allBelow_B {s t : St n} {p : Fin n} (hs : IsPivot s p)
    (ht1 : ∀ q, p < q → col t q = ev q) (ht2 : prof (col t p) < prof (col s p))
    {w : Word (Gen n)} (hw : ∀ y ∈ FreeMonoid.toList w, IsXω y ∧ ∀ i ∈ gidx y, i ≤ p) :
    AllBelow (level s) t w := by
  apply AllBelow.of_inv
    (fun u => (∀ q, p < q → col u q = ev q) ∧ prof (col u p) < prof (col s p))
  · intro u hu; exact level_lt_of_cols hs hu.1 (Or.inr hu.2)
  · intro y hy u hu
    obtain ⟨hxω, hle⟩ := hw y hy
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [col_mul, hu.1 q hq, sm_sem]
      exact mat_mulVec_ev_of_ne y q (fun i hi => ne_of_lt (lt_of_le_of_lt (hle i hi) hq))
    · rw [col_mul, sm_sem, prof_mat_Xω y hxω (hasNum_exists u p)]; exact hu.2
  · exact ⟨ht1, ht2⟩

/-! ### Closing squares -/

/-- Subcase 1.1: the syllable of `s` is `x`, so `t = r`. -/
theorem sq_triv {s : St n} (hs : s ≠ 1) {x : Gen n}
    (h : Derivable (Rel n) (FreeMonoid.of x) (syl s)) : Square s x := by
  have ht : ⟪syl s⟫ * s = sem n x * s := by
    rw [← derivable_sound (fun _ _ h => sound h) h, FreeMonoid.lift_eval_of]
  refine ⟨sem n x * s, 1, 1, NormalPath.refl _, by rw [map_one, one_mul, ht], ?_,
    by simpa using h⟩
  exact AllBelow.one' (level_syl_lt hs)

/-- A square whose right edge is the one normal edge out of `r = x s`. -/
theorem sq_gen {s : St n} {x : Gen n} (hr : sem n x * s ≠ 1)
    {u G' : Word (Gen n)} (hsyl : syl (sem n x * s) = u)
    (hrel : Derivable (Rel n) (u * FreeMonoid.of x) (G' * syl s))
    (hG : AllBelow (level s) (⟪syl s⟫ * s) G') : Square s x := by
  have hsnd := derivable_sound (fun _ _ h => sound h) hrel
  rw [map_mul, map_mul, FreeMonoid.lift_eval_of] at hsnd
  refine ⟨⟪u⟫ * (sem n x * s), u, G', ?_, ?_, hG, hrel⟩
  · have := NormalPath.step hr (NormalPath.refl (⟪syl (sem n x * s)⟫ * (sem n x * s)))
    rw [one_mul, hsyl] at this
    exact this
  · rw [← mul_assoc, ← hsnd, mul_assoc]

/-- A retrograde edge (Definition 40): the normal edge out of `r = x s` is
inverse to `x`. -/
theorem sq_retro {s : St n} (hs : s ≠ 1) {x : Gen n} (hr : sem n x * s ≠ 1)
    {u : Word (Gen n)} (hsyl : syl (sem n x * s) = u)
    (hrel : Derivable (Rel n) (u * FreeMonoid.of x) 1) : Square s x := by
  have hsnd := derivable_sound (fun _ _ h => sound h) hrel
  rw [map_mul, map_one, FreeMonoid.lift_eval_of] at hsnd
  have hback : ⟪u⟫ * (sem n x * s) = s := by rw [← mul_assoc, hsnd, one_mul]
  refine ⟨⟪syl s⟫ * s, syl s * u, 1, ?_, by rw [map_one, one_mul],
    AllBelow.one' (level_syl_lt hs), ?_⟩
  · have h1 := NormalPath.step hs (NormalPath.refl (⟪syl s⟫ * s))
    rw [one_mul] at h1
    have h2 : NormalPath (⟪syl (sem n x * s)⟫ * (sem n x * s)) (syl s) (⟪syl s⟫ * s) := by
      rw [hsyl, hback]; exact h1
    have := NormalPath.step hr h2
    rwa [hsyl] at this
  · rw [one_mul, mul_assoc]
    simpa using (Derivable.refl (syl s)).mul hrel

/-! ### Pivot columns and syllables -/

theorem isPivot_mul {s : St n} {p : Fin n} (hs : IsPivot s p) {y : Gen n}
    (hy : ∀ i ∈ gidx y, i ≤ p) (hne : mat y *ᵥ col s p ≠ ev p) : IsPivot (sem n y * s) p := by
  refine ⟨by rwa [col_mul, sm_sem], fun q hq => ?_⟩
  rw [col_mul, sm_sem, hs.2 q hq]
  exact mat_mulVec_ev_of_ne y q (fun i hi => ne_of_lt (lt_of_le_of_lt (hy i hi) hq))

theorem hasNum_ev (p : Fin n) : HasNum (ev p) 0 (fun a => if a = p then 1 else 0) := by
  intro a; by_cases ha : a = p <;> simp [ev, ha]

/-- A column with an odd numerator entry at a positive exponent is not a
basis vector. -/
theorem ne_ev_of_hasNum {v : Fin n → ℂ} {K : ℕ} {w : Fin n → ZOmega} (h : HasNum v K w)
    (hK : 0 < K) (hodd : ∃ j, IsOdd (w j)) (p : Fin n) : v ≠ ev p := by
  intro hv
  have h1 : lde v = K := lde_eq h (Or.inr hodd)
  have h2 : lde v = 0 := by rw [hv]; exact lde_eq (hasNum_ev p) (Or.inl rfl)
  omega

theorem syl_H_of {r : St n} {p : Fin n} (hr : IsPivot r p) {K : ℕ} {w : Fin n → ZOmega}
    (hw : HasNum (col r p) K w) (hK : 0 < K) {a b : Fin n} (hf : FirstTwo w a b) :
    syl r = H a b hf.1 * ω a ^ zexp (w a) (w b) := by
  rw [syl_eq hr, sylCol_H hw hK (lde_eq hw (Or.inr ⟨a, hf.2.1⟩)) hf]

theorem syl_unit_lt_of {r : St n} {p c : Fin n} (hr : IsPivot r p) {w : Fin n → ZOmega}
    (hw : HasNum (col r p) 0 w) (hc : w c ≠ 0) (hz : ∀ a, a ≠ c → w a = 0) (hcp : c < p) :
    syl r = ω p ^ (8 - uexp (w c)) * X c p hcp := by
  rw [syl_eq hr, sylCol_unit_lt hw hc hz hcp]

theorem syl_unit_eq_of {r : St n} {p : Fin n} (hr : IsPivot r p) {w : Fin n → ZOmega}
    (hw : HasNum (col r p) 0 w) (hc : w p ≠ 0) (hz : ∀ a, a ≠ p → w a = 0) :
    syl r = ω p ^ (8 - uexp (w p)) := by
  rw [syl_eq hr, sylCol_unit_eq hw hc hz]

/-! ### The pivot column of `s` -/

theorem hasNum_num (s : St n) (p : Fin n) :
    HasNum (col s p) (lde (col s p)) (num (col s p)) := num_spec (hasNum_exists s p)

/-- `k = 0`: the pivot column is `ωᵐ e_c` with `c ≤ p` (Lemma 14). -/
theorem unit_data {s : St n} {p : Fin n} (hp : IsPivot s p) (hk : lde (col s p) = 0) :
    ∃ c, c ≤ p ∧ nrm0 (num (col s p) c) = 1 ∧ ∀ a, a ≠ c → num (col s p) a = 0 := by
  have hw := hasNum_num s p
  rw [hk] at hw
  obtain ⟨c, hc1, hc0⟩ := unit_of_sum (col_unit s p) hw
  refine ⟨c, ?_, hc1, hc0⟩
  by_contra h
  have := hasNum_zero_of_entry hp hw (not_le.1 h)
  rw [this] at hc1; simp [nrm0] at hc1

/-- `k > 0`: the first two odd entries `α < β ≤ p` (Lemma 13). -/
theorem odd_data {s : St n} {p : Fin n} (hp : IsPivot s p) (hk : 0 < lde (col s p)) :
    ∃ a b, FirstTwo (num (col s p)) a b ∧ b ≤ p := by
  have hw := hasNum_num s p
  have hev := even_card_odd (col_unit s p) hw hk
  obtain ⟨j0, hj0⟩ := exists_odd hw hk
  have h2 : 2 ≤ (oddSet (num (col s p))).card := by
    have : 0 < (oddSet (num (col s p))).card := Finset.card_pos.2 ⟨j0, mem_oddSet.2 hj0⟩
    have hev' : Even (oddSet (num (col s p))).card := hev
    obtain ⟨r, hr⟩ := hev'
    omega
  obtain ⟨a, b, hf⟩ := exists_firstTwo h2
  refine ⟨a, b, hf, ?_⟩
  by_contra h
  have := hasNum_zero_of_entry hp hw (not_le.1 h)
  have h3 := hf.2.2.1
  rw [this] at h3; exact not_isOdd_zero h3

/-- After the syllable of a column with `k = 0`, the state is the identity
from column `p` on. -/
theorem t_above {s : St n} {p : Fin n} (hp : IsPivot s p) (hk : lde (col s p) = 0) :
    ∀ q, p ≤ q → col (⟪syl s⟫ * s) q = ev q := by
  obtain ⟨h1, h2, -⟩ := syl_cols hp
  intro q hq
  rcases hq.lt_or_eq with hq | rfl
  · exact h1 q hq
  · exact h2 hk

/-- After the syllable of a column with `k > 0`, the columns beyond `p` are
unchanged and column `p` has a smaller profile. -/
theorem t_below {s : St n} {p : Fin n} (hp : IsPivot s p) (hk : 0 < lde (col s p)) :
    (∀ q, p < q → col (⟪syl s⟫ * s) q = ev q) ∧ prof (col (⟪syl s⟫ * s) p) < prof (col s p) :=
  ⟨(syl_cols hp).1, (syl_cols hp).2.2 hk⟩

/-! ### `H` on two entries -/

theorem hasNum_H_gen {v : Fin n → ℂ} {k : ℕ} {w : Fin n → ZOmega} (h : HasNum v k w)
    {a b : Fin n} (hab : a ≠ b) (d : ℕ) (hd : d ≤ 2) {e1 e2 : ZOmega}
    (h1 : w a + w b = δz ^ d * e1) (h2 : w a - w b = δz ^ d * e2) :
    HasNum (twoLevel a b Hmat *ᵥ v) (k + (2 - d))
      (Function.update (Function.update (fun c => δz ^ (2 - d) * w c) a (ηz * e1)) b
        (ηz * e2)) := by
  intro j
  have hη : δ ^ 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = toC ηz := δ_sq_mul_invSqrt2
  have E1 : toC (w a) + toC (w b) = δ ^ d * toC e1 := by
    rw [← map_add, h1, map_mul, map_pow, toC_δz']
  have E2 : toC (w a) - toC (w b) = δ ^ d * toC e2 := by
    rw [← map_sub, h2, map_mul, map_pow, toC_δz']
  have ha := h a
  have hb := h b
  have hdd : δ ^ (2 - d) * δ ^ d = δ ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hd]
  rw [twoLevel_mulVec hab]
  simp only [Function.update_apply]
  split_ifs with hjb hja
  · rw [Hmat_10, Hmat_11, map_mul, ← hη, pow_add]
    linear_combination (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * ha -
      (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * hb +
      (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * E2 +
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * toC e2) * hdd
  · rw [Hmat_00, Hmat_01, map_mul, ← hη, pow_add]
    linear_combination (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * ha +
      (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * hb +
      (δ ^ (2 - d) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * E1 +
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * toC e1) * hdd
  · rw [map_mul, map_pow, toC_δz', ← h j, pow_add]
    ring

end

end QCert.Greylyn
