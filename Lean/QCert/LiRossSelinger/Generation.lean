/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): generation (Theorem 3.5)

The exact synthesis of Section 3: an element `M` of `Oₙ(ℤ[1/2])` whose
columns after `J` are standard basis vectors is reduced column by column.
Its column `J` is a unit vector `v` supported on `0, …, J`.  With `k` the
least denominator exponent of `v` (Definition 2.2) and `2^k v` integral:

* if `k > 0`, the number of odd entries of `2^k v` is a positive multiple
  of four (Lemma 3.2); four of them are made even by a syllable
  `K_[a,b,c,d] (−1)_[a]^τ … (−1)_[d]^τ` (Lemma 3.1), so the pair
  (`k`, number of odd entries) decreases;
* if `k = 0`, `v = ±e_a` (Lemma 3.3), and `X_[a,J] (−1)_[a]^τ` or
  `(−1)_[J]` moves it to `e_J` (Lemma 3.4).

Every syllable touches only indices `≤ J`, so the later columns stay put.
-/
import QCert.LiRossSelinger.Rows
import QCert.LiRossSelinger.Soundness

namespace QCert.LiRossSelinger

open Matrix Classical

variable {n : ℕ}

noncomputable section

/-- The matrix of an element of `Oₙ(ℤ[1/2])`. -/
abbrev mat (U : O_ZHalf n) : Matrix (Fin n) (Fin n) ℝ :=
  ((U : unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)

theorem mat_mul (U V : O_ZHalf n) : mat (U * V) = mat U * mat V := rfl

/-- The columns `i ≥ J` are the standard basis vectors `e_i`. -/
def FixCols (M : Matrix (Fin n) (Fin n) ℝ) (J : ℕ) : Prop :=
  ∀ i : Fin n, J ≤ i.val → ∀ r, M r i = if r = i then 1 else 0

theorem eq_one_of_fixCols_zero (U : O_ZHalf n) (h : FixCols (mat U) 0) : U = 1 := by
  apply Subtype.ext; apply Subtype.ext
  ext r i
  exact (h i (Nat.zero_le _) r).trans (one_apply (i := r) (j := i)).symm

/-- Columns of an orthogonal matrix are orthonormal. -/
theorem col_orth (U : O_ZHalf n) (i j : Fin n) :
    ∑ r, mat U r i * mat U r j = if i = j then 1 else 0 := by
  have h := mem_unitaryGroup_iff'.1 (U : unitaryGroup (Fin n) ℝ).2
  have := congrFun (congrFun h i) j
  rw [mul_apply, one_apply] at this
  simpa [star_apply] using this

/-- The column `J` vanishes below the fixed columns. -/
theorem col_zero_above (U : O_ZHalf n) {J : ℕ} (hJ : J < n) (hfix : FixCols (mat U) (J + 1))
    (r : Fin n) (hr : J < r.val) : mat U r ⟨J, hJ⟩ = 0 := by
  have := col_orth U r ⟨J, hJ⟩
  rw [if_neg (fun h => by rw [h] at hr; exact lt_irrefl _ hr)] at this
  simp only [hfix r hr, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at this
  exact this

/-! ## Integer columns -/

/-- `2^k v` is integral. -/
def IntAt (v : Fin n → ℝ) (k : ℕ) : Prop := ∀ r, ∃ z : ℤ, 2 ^ k * v r = z

theorem intAt_exists (v : Fin n → ℝ) (hv : ∀ r, v r ∈ ZHalf) : ∃ k, IntAt v k := by
  choose k z hz using fun r => exists_of_mem_ZHalf (hv r)
  let K := Finset.univ.sup k
  refine ⟨K, fun r => ⟨z r * 2 ^ (K - k r), ?_⟩⟩
  have hle : k r ≤ K := Finset.le_sup (Finset.mem_univ r)
  rw [hz r]
  have : (2 : ℝ) ^ K = 2 ^ (K - k r) * 2 ^ k r := by rw [← pow_add, Nat.sub_add_cancel hle]
  rw [this]; push_cast; field_simp

theorem intAt_mono {v : Fin n → ℝ} {k l : ℕ} (h : IntAt v k) (hkl : k ≤ l) : IntAt v l := by
  intro r
  obtain ⟨z, hz⟩ := h r
  refine ⟨z * 2 ^ (l - k), ?_⟩
  rw [show (2 : ℝ) ^ l = 2 ^ (l - k) * 2 ^ k by rw [← pow_add, Nat.sub_add_cancel hkl], mul_assoc,
    hz]
  push_cast; ring

/-- The odd entries of `2^k v`. -/
def oddSet (v : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun r => ∃ z : ℤ, 2 ^ k * v r = z ∧ Odd z

theorem not_odd_of_intAt_pred {v : Fin n → ℝ} {k : ℕ} (h : IntAt v (k + 1))
    (heven : ∀ r, r ∉ oddSet v (k + 1)) : IntAt v k := by
  intro r
  obtain ⟨z, hz⟩ := h r
  have hz2 : Even z := by
    by_contra hodd
    exact heven r (Finset.mem_filter.2 ⟨Finset.mem_univ _, z, hz, Int.not_even_iff_odd.1 hodd⟩)
  obtain ⟨y, rfl⟩ := hz2
  refine ⟨y, ?_⟩
  have : (2 : ℝ) ^ (k + 1) * v r = 2 * (2 ^ k * v r) := by ring
  rw [this] at hz; push_cast at hz; linarith

theorem sq_mod_four (z : ℤ) : 4 ∣ z ^ 2 - (if Odd z then 1 else 0) := by
  rcases Int.even_or_odd z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [if_neg (Int.not_odd_iff_even.2 ⟨y, rfl⟩)]; exact ⟨y ^ 2, by ring⟩
  · rw [if_pos ⟨y, rfl⟩]; exact ⟨y ^ 2 + y, by ring⟩

/-- Lemma 3.2: a unit vector with least denominator exponent `k > 0` has a
positive multiple of four odd entries in `2^k v`. -/
theorem four_dvd_card_oddSet {v : Fin n → ℝ} (hnorm : ∑ r, v r * v r = 1) {k : ℕ} (hk : 0 < k)
    (h : IntAt v k) : 4 ∣ (oddSet v k).card := by
  choose z hz using h
  have hsum : ∑ r, (z r : ℝ) ^ 2 = 4 ^ k := by
    have : ∀ r, (z r : ℝ) ^ 2 = 4 ^ k * (v r * v r) := by
      intro r; rw [← hz r]; rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
    simp only [this, ← Finset.mul_sum, hnorm, mul_one]
  have hsumZ : ∑ r, z r ^ 2 = 4 ^ k := by exact_mod_cast hsum
  have hodd : ∀ r, Odd (z r) ↔ r ∈ oddSet v k := by
    intro r
    constructor
    · intro ho; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, z r, hz r, ho⟩
    · intro hm
      obtain ⟨_, y, hy, hyo⟩ := Finset.mem_filter.1 hm
      have : z r = y := by exact_mod_cast (hz r).symm.trans hy
      rwa [this]
  have hcard : ((oddSet v k).card : ℤ) = ∑ r, (if Odd (z r) then 1 else 0 : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext r; simp [hodd r]
  have h4 : (4 : ℤ) ∣ ∑ r, (z r ^ 2 - if Odd (z r) then 1 else 0) :=
    Finset.dvd_sum fun r _ => sq_mod_four (z r)
  rw [Finset.sum_sub_distrib, hsumZ, ← hcard] at h4
  have h4k : (4 : ℤ) ∣ 4 ^ k := dvd_pow_self 4 (by omega)
  have := (Int.dvd_sub h4k h4)
  rw [sub_sub_cancel] at this
  exact_mod_cast this

/-- Lemma 3.3: an integral unit vector is `±e_a`. -/
theorem int_unit {v : Fin n → ℝ} (hnorm : ∑ r, v r * v r = 1) (h : IntAt v 0) :
    ∃ a, (v a = 1 ∨ v a = -1) ∧ ∀ r, r ≠ a → v r = 0 := by
  choose z hz using h
  simp only [pow_zero, one_mul] at hz
  have hsumZ : ∑ r, z r * z r = 1 := by
    have : ∑ r, (z r : ℝ) * z r = 1 := by simpa [hz] using hnorm
    exact_mod_cast this
  have hnonneg : ∀ r, 0 ≤ z r * z r := fun r => mul_self_nonneg _
  obtain ⟨a, ha⟩ : ∃ a, z a ≠ 0 := by
    by_contra hall; push Not at hall
    simp [hall] at hsumZ
  have hsq : z a * z a ≤ 1 := by
    rw [← hsumZ]; exact Finset.single_le_sum (fun r _ => hnonneg r) (Finset.mem_univ a)
  have hpos : 0 < z a * z a := mul_self_pos.2 ha
  have h1 : z a * z a = 1 := by omega
  have hrest : ∀ r, r ≠ a → z r = 0 := by
    intro r hr
    have : z a * z a + z r * z r ≤ 1 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {a, r})
        (fun i _ _ => hnonneg i)
      rw [Finset.sum_pair (Ne.symm hr)] at this
      linarith
    have : z r * z r = 0 := by nlinarith [hnonneg r]
    exact mul_self_eq_zero.1 this
  refine ⟨a, ?_, fun r hr => by rw [hz r, hrest r hr]; simp⟩
  have : z a = 1 ∨ z a = -1 := by
    exact Int.eq_one_or_neg_one_of_mul_eq_one h1
  rcases this with h | h
  · left; rw [hz a, h]; simp
  · right; rw [hz a, h]; simp

/-! ## One syllable -/

/-- Negating the rows in a list without repetition. -/
theorem negs_mul (l : List (Fin n)) (hl : l.Nodup) (M : Matrix (Fin n) (Fin n) ℝ) (r j : Fin n) :
    ((l.map (fun x => genMat (Gen.neg x))).prod * M) r j = if r ∈ l then -M r j else M r j := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, genMat_neg_mul, ih hl.2]
    by_cases hr : r = x
    · subst hr; simp [hl.1]
    · simp [hr]

theorem four_dvd_combos (u₁ u₂ u₃ u₄ : ℤ) (h₁ : u₁ % 4 = 1) (h₂ : u₂ % 4 = 1) (h₃ : u₃ % 4 = 1)
    (h₄ : u₄ % 4 = 1) :
    4 ∣ u₁ + u₂ + u₃ + u₄ ∧ 4 ∣ u₁ - u₂ + u₃ - u₄ ∧ 4 ∣ u₁ + u₂ - u₃ - u₄ ∧
      4 ∣ u₁ - u₂ - u₃ + u₄ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The sign that makes an odd integer `1` mod `4`. -/
def fix4 (z : ℤ) : ℤ := if z % 4 = 3 then -z else z

theorem fix4_mod {z : ℤ} (hz : Odd z) : fix4 z % 4 = 1 := by
  obtain ⟨y, rfl⟩ := hz
  unfold fix4; split_ifs <;> omega

/-- Lemma 3.1: the syllable `K_[a,b,c,d] (−1)^τ` on four odd entries of
`2^k v`: those become even, the others are unchanged, and so is every column
vanishing at `a, b, c, d`. -/
theorem syllable {k : ℕ} {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (z : Fin n → ℤ)
    (hz : ∀ r, 2 ^ k * M r j = z r) (ha : Odd (z a)) (hb : Odd (z b)) (hc : Odd (z c))
    (hd : Odd (z d)) :
    let l := [a, b, c, d].filter (fun x => decide (z x % 4 = 3))
    let M' := genMat (Gen.k a b c d hab hbc hcd) * ((l.map (fun x => genMat (Gen.neg x))).prod * M)
    (∀ r, r ∉ [a, b, c, d] → M' r j = M r j) ∧
      (∀ x ∈ [a, b, c, d], ∃ y : ℤ, 2 ^ k * M' x j = y ∧ Even y) ∧
      (∀ i, (∀ x ∈ [a, b, c, d], M x i = 0) → ∀ r, M' r i = M r i) := by
  intro l M'
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simp only [ne_eq, Fin.ext_iff]; simp only [Fin.lt_def] at hab hbc hcd; omega
  have hnd : [a, b, c, d].Nodup := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
    simp [List.nodup_cons, h1, h2, h3, h4, h5, h6]
  have hl : l.Nodup := hnd.filter _
  have hmem : ∀ x, x ∈ l ↔ x ∈ [a, b, c, d] ∧ z x % 4 = 3 := by
    intro x; simp [l, List.mem_filter]
  -- the entries after the signs
  set Ms := (l.map (fun x => genMat (Gen.neg x))).prod * M with hMs
  have hS : ∀ r i, Ms r i = if r ∈ l then -M r i else M r i := fun r i => negs_mul l hl M r i
  have hK : ∀ r i, M' r i =
      if r = a then (Ms a i + Ms b i + Ms c i + Ms d i) / 2
      else if r = b then (Ms a i - Ms b i + Ms c i - Ms d i) / 2
      else if r = c then (Ms a i + Ms b i - Ms c i - Ms d i) / 2
      else if r = d then (Ms a i - Ms b i - Ms c i + Ms d i) / 2
      else Ms r i := fun r i => genMat_k_mul hab hbc hcd Ms r i
  have hnotl : ∀ r, r ∉ [a, b, c, d] → r ∉ l := fun r hr h => hr ((hmem r).1 h).1
  refine ⟨fun r hr => ?_, fun x hx => ?_, fun i hi r => ?_⟩
  · have hr' : r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr
    rw [hK, if_neg hr'.1, if_neg hr'.2.1, if_neg hr'.2.2.1, if_neg hr'.2.2.2, hS,
      if_neg (hnotl r hr)]
  · -- the four rows become even
    have hf : ∀ x ∈ [a, b, c, d], 2 ^ k * Ms x j = (fix4 (z x) : ℝ) := by
      intro x hx
      rw [hS]
      by_cases h3 : z x % 4 = 3
      · rw [if_pos ((hmem x).2 ⟨hx, h3⟩), fix4, if_pos h3]; push_cast; rw [← hz x]; ring
      · rw [if_neg (fun h => h3 ((hmem x).1 h).2), fix4, if_neg h3, hz x]
    have fa := hf a (by simp); have fb := hf b (by simp)
    have fc := hf c (by simp); have fd := hf d (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := four_dvd_combos _ _ _ _ (fix4_mod ha) (fix4_mod hb) (fix4_mod hc)
      (fix4_mod hd)
    have even_of : ∀ (e : ℤ) (q : ℝ), 4 ∣ e → 2 ^ k * q = (e : ℝ) / 2 →
        ∃ y : ℤ, 2 ^ k * q = y ∧ Even y := by
      intro e q he hq
      obtain ⟨t, rfl⟩ := he
      exact ⟨2 * t, by rw [hq]; push_cast; ring, ⟨t, by ring⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine even_of _ _ h1 ?_
      rw [hK, if_pos rfl]; push_cast; rw [← fa, ← fb, ← fc, ← fd]; ring
    · refine even_of _ _ h2 ?_
      rw [hK, if_neg (Ne.symm hne.1), if_pos rfl]; push_cast; rw [← fa, ← fb, ← fc, ← fd]; ring
    · refine even_of _ _ h3 ?_
      rw [hK, if_neg (Ne.symm hne.2.1), if_neg (Ne.symm hne.2.2.2.1), if_pos rfl]
      push_cast; rw [← fa, ← fb, ← fc, ← fd]; ring
    · refine even_of _ _ h4 ?_
      rw [hK, if_neg (Ne.symm hne.2.2.1), if_neg (Ne.symm hne.2.2.2.2.1),
        if_neg (Ne.symm hne.2.2.2.2.2), if_pos rfl]
      push_cast; rw [← fa, ← fb, ← fc, ← fd]; ring
  · -- a column vanishing at `a, b, c, d` is unchanged
    have h0 : ∀ x ∈ [a, b, c, d], Ms x i = 0 := by
      intro x hx; rw [hS, hi x hx]; simp
    have za := h0 a (by simp); have zb := h0 b (by simp)
    have zc := h0 c (by simp); have zd := h0 d (by simp)
    rw [hK]
    by_cases hra : r = a
    · subst hra; rw [if_pos rfl, za, zb, zc, zd, hi r (by simp)]; norm_num
    rw [if_neg hra]
    by_cases hrb : r = b
    · subst hrb; rw [if_pos rfl, za, zb, zc, zd, hi r (by simp)]; norm_num
    rw [if_neg hrb]
    by_cases hrc : r = c
    · subst hrc; rw [if_pos rfl, za, zb, zc, zd, hi r (by simp)]; norm_num
    rw [if_neg hrc]
    by_cases hrd : r = d
    · subst hrd; rw [if_pos rfl, za, zb, zc, zd, hi r (by simp)]; norm_num
    rw [if_neg hrd, hS, if_neg (hnotl r (by simp [hra, hrb, hrc, hrd]))]

/-! ## The column reduction -/

theorem mat_word (l : List (Gen n)) (U : O_ZHalf n) :
    mat (FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * U) = (l.map genMat).prod * mat U := by
  rw [mat_mul]
  congr 1
  exact (sem_word _).trans (by rw [FreeMonoid.toList_ofList])

theorem col_mem (U : O_ZHalf n) (j : Fin n) : ∀ r, (fun r => mat U r j) r ∈ ZHalf :=
  fun r => (mem_unitaryOver).1 U.2 r j

theorem col_norm (U : O_ZHalf n) (j : Fin n) : ∑ r, mat U r j * mat U r j = 1 := by
  rw [col_orth U j j, if_pos rfl]

/-- The measure of the column reduction: least denominator exponent and
number of odd entries of column `j`. -/
def measure (U : O_ZHalf n) (j : Fin n) : ℕ :=
  Nat.find (intAt_exists _ (col_mem U j)) * (n + 1) +
    (oddSet (fun r => mat U r j) (Nat.find (intAt_exists _ (col_mem U j)))).card

theorem oddSet_card_le (v : Fin n → ℝ) (k : ℕ) : (oddSet v k).card ≤ n :=
  (Finset.card_le_univ _).trans (by simp)

/-- An odd entry of `2^k v` is nonzero. -/
theorem ne_zero_of_mem_oddSet {v : Fin n → ℝ} {k : ℕ} {r : Fin n} (h : r ∈ oddSet v k) :
    v r ≠ 0 := by
  obtain ⟨_, y, hy, hyo⟩ := Finset.mem_filter.1 h
  intro h0
  rw [h0, mul_zero] at hy
  have : y = 0 := by exact_mod_cast hy.symm
  rw [this] at hyo; exact (Int.not_odd_iff_even.2 ⟨0, rfl⟩) hyo

theorem le_of_ne_zero (U : O_ZHalf n) {J : ℕ} (hJ : J < n) (hfix : FixCols (mat U) (J + 1))
    {r : Fin n} (hr : mat U r ⟨J, hJ⟩ ≠ 0) : r.val ≤ J := by
  by_contra h; exact hr (col_zero_above U hJ hfix r (by omega))

/-- A column `e_J` and the later columns fixed: `FixCols J`. -/
theorem fixCols_of_col (M : Matrix (Fin n) (Fin n) ℝ) {J : ℕ} (hJ : J < n) (hfix : FixCols M (J + 1))
    (hcol : ∀ r, M r ⟨J, hJ⟩ = if r = ⟨J, hJ⟩ then 1 else 0) : FixCols M J := by
  intro i hi r
  rcases Nat.eq_or_lt_of_le hi with h | h
  · have : i = ⟨J, hJ⟩ := Fin.ext h.symm
    subst this; exact hcol r
  · exact hfix i h r

theorem colStep (J : ℕ) (hJ : J < n) : ∀ (N : ℕ) (U : O_ZHalf n), measure U ⟨J, hJ⟩ = N →
    FixCols (mat U) (J + 1) → ∃ w : Word (Gen n), FixCols (mat (FreeMonoid.lift (sem n) w * U)) J := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro U hN hfix
  set jJ : Fin n := ⟨J, hJ⟩ with hjJ
  set v : Fin n → ℝ := fun r => mat U r jJ with hv
  have hex := intAt_exists v (col_mem U jJ)
  set k := Nat.find hex with hkdef
  have hk : IntAt v k := Nat.find_spec hex
  have hnorm : ∑ r, v r * v r = 1 := col_norm U jJ
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `v = ±e_a`
    rw [hk0] at hk
    obtain ⟨a, hva, hrest⟩ := int_unit hnorm hk
    have haJ : a.val ≤ J := le_of_ne_zero U hJ hfix (by
      show v a ≠ 0; rcases hva with h | h <;> rw [h] <;> norm_num)
    rcases Nat.eq_or_lt_of_le haJ with haJ | haJ
    · have ha : a = jJ := Fin.ext haJ
      subst ha
      rcases hva with h1 | h1
      · refine ⟨1, ?_⟩
        rw [map_one, one_mul]
        refine fixCols_of_col _ hJ hfix fun r => ?_
        by_cases hr : r = jJ
        · rw [if_pos hr, hr]; exact h1
        · rw [if_neg hr]; exact hrest r hr
      · refine ⟨FreeMonoid.ofList [Gen.neg jJ], ?_⟩
        rw [mat_word]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        refine fixCols_of_col _ hJ ?_ fun r => ?_
        · intro i hi r
          rw [genMat_neg_mul, hfix i hi r]
          have : jJ ≠ i := fun h => by subst h; simp [hjJ] at hi
          by_cases hr : r = jJ
          · subst hr; simp [this]
          · simp [hr]
        · rw [genMat_neg_mul]
          by_cases hr : r = jJ
          · rw [if_pos hr, if_pos hr, hr]; show -v jJ = 1; rw [h1]; norm_num
          · rw [if_neg hr, if_neg hr]; exact hrest r hr
    · -- `a < J`
      have hne : a ≠ jJ := fun h => by rw [h] at haJ; exact lt_irrefl _ haJ
      have haJ' : a < jJ := haJ
      let l : List (Gen n) := Gen.x a jJ haJ' :: (if v a = -1 then [Gen.neg a] else [])
      refine ⟨FreeMonoid.ofList l, ?_⟩
      rw [mat_word]
      have hsign : ∀ i r, (((if v a = -1 then [Gen.neg a] else []).map genMat).prod * mat U) r i =
          if r = a ∧ v a = -1 then -mat U r i else mat U r i := by
        intro i r
        split_ifs with h1 h2 h2
        · simp [genMat_neg_mul, h2.1]
        · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [genMat_neg_mul, if_neg (fun h => h2 ⟨h, h1⟩)]
        · exact absurd h2.2 h1
        · simp
      have hcolX : ∀ i r, ((l.map genMat).prod * mat U) r i =
          if r = a then mat U jJ i
          else if r = jJ then (if v a = -1 then -mat U a i else mat U a i)
          else mat U r i := by
        intro i r
        simp only [l, List.map_cons, List.prod_cons, Matrix.mul_assoc]
        rw [genMat_x_mul, hsign, hsign, hsign]
        by_cases hra : r = a
        · simp [hra, hne.symm]
        · by_cases hrJ : r = jJ
          · simp [hrJ, Ne.symm hne]
          · simp [hra, hrJ]
      refine fixCols_of_col _ hJ ?_ fun r => ?_
      · intro i hi r
        have hai : a ≠ i := fun h => by subst h; omega
        have hJi : jJ ≠ i := fun h => by subst h; simp [hjJ] at hi
        rw [hcolX, hfix i hi r, hfix i hi jJ, hfix i hi a]
        by_cases hra : r = a
        · subst hra; simp [hai, hJi]
        · by_cases hrJ : r = jJ
          · subst hrJ; simp [hra, hJi, hai]
          · simp [hra, hrJ]
      · rw [hcolX]
        have hvJ : v jJ = 0 := hrest jJ (Ne.symm hne)
        by_cases hra : r = a
        · rw [if_pos hra, if_neg (by rw [hra]; exact hne)]
          exact hvJ
        · rw [if_neg hra]
          by_cases hrJ : r = jJ
          · rw [if_pos hrJ, if_pos hrJ]
            show (if v a = -1 then -v a else v a) = 1
            rcases hva with h | h <;> rw [h] <;> norm_num
          · rw [if_neg hrJ, if_neg hrJ]; exact hrest r hra
  · -- `k > 0`: a syllable on four odd entries
    set S := oddSet v k with hSdef
    have h4 : 4 ∣ S.card := four_dvd_card_oddSet hnorm hkpos hk
    have hS0 : S.card ≠ 0 := by
      intro h0
      have hk1 : IntAt v (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]; exact hk
      have hev : ∀ r, r ∉ oddSet v (k - 1 + 1) := by
        rw [Nat.sub_add_cancel hkpos]; intro r hr
        rw [Finset.card_eq_zero] at h0
        have : r ∈ S := hr
        rw [h0] at this; simp at this
      exact Nat.find_min hex (by omega : k - 1 < k) (not_odd_of_intAt_pred hk1 hev)
    have hcard : 4 ≤ S.card := Nat.le_of_dvd (Nat.pos_of_ne_zero hS0) h4
    let e := S.orderEmbOfFin rfl
    have hmemS : ∀ i, e i ∈ S := fun i => Finset.orderEmbOfFin_mem S rfl i
    let a := e ⟨0, by omega⟩
    let b := e ⟨1, by omega⟩
    let c := e ⟨2, by omega⟩
    let d := e ⟨3, by omega⟩
    have hab : a < b := e.strictMono (by simp [Fin.lt_def])
    have hbc : b < c := e.strictMono (by simp [Fin.lt_def])
    have hcd : c < d := e.strictMono (by simp [Fin.lt_def])
    choose z hz using hk
    have hodd : ∀ x ∈ S, Odd (z x) := by
      intro x hx
      obtain ⟨_, y, hy, hyo⟩ := Finset.mem_filter.1 hx
      have : z x = y := by exact_mod_cast (hz x).symm.trans hy
      rwa [this]
    have hsub : ∀ x ∈ [a, b, c, d], x ∈ S := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact hmemS _
    obtain ⟨p1, p2, p3⟩ := syllable hab hbc hcd (mat U) jJ z hz (hodd a (hsub a (by simp)))
      (hodd b (hsub b (by simp))) (hodd c (hsub c (by simp))) (hodd d (hsub d (by simp)))
    set lsign := [a, b, c, d].filter (fun x => decide (z x % 4 = 3))
    set U' := FreeMonoid.lift (sem n) (FreeMonoid.ofList
      (Gen.k a b c d hab hbc hcd :: lsign.map Gen.neg)) * U with hU'
    have hmat : mat U' = genMat (Gen.k a b c d hab hbc hcd) *
        ((lsign.map (fun x => genMat (Gen.neg x))).prod * mat U) := by
      rw [hU', mat_word, List.map_cons, List.prod_cons, List.map_map, Matrix.mul_assoc]; rfl
    -- the odd entries are at indices `≤ J`
    have hle : ∀ x ∈ S, x.val ≤ J := fun x hx =>
      le_of_ne_zero U hJ hfix (ne_zero_of_mem_oddSet (v := v) hx)
    have hfix' : FixCols (mat U') (J + 1) := by
      intro i hi r
      rw [hmat, p3 i (fun x hx => by
        rw [hfix i hi x, if_neg (fun h => by have := hle x (hsub x hx); rw [h] at this; omega)]) r]
      exact hfix i hi r
    -- the new column
    set v' : Fin n → ℝ := fun r => mat U' r jJ with hv'
    have hv'eq : ∀ r, r ∉ [a, b, c, d] → v' r = v r := fun r hr => by
      show mat U' r jJ = mat U r jJ; rw [hmat]; exact p1 r hr
    have hint' : IntAt v' k := by
      intro r
      by_cases hr : r ∈ [a, b, c, d]
      · obtain ⟨y, hy, _⟩ := p2 r hr
        exact ⟨y, by show 2 ^ k * mat U' r jJ = y; rw [hmat]; exact hy⟩
      · exact ⟨z r, by rw [hv'eq r hr]; exact hz r⟩
    have hodd' : oddSet v' k ⊆ S \ {a, b, c, d} := by
      intro r hr
      rw [Finset.mem_sdiff]
      by_cases hr4 : r ∈ [a, b, c, d]
      · exfalso
        obtain ⟨y, hy, hye⟩ := p2 r hr4
        obtain ⟨_, y', hy', hyo⟩ := Finset.mem_filter.1 hr
        have : y' = y := by
          have h1 : (2 : ℝ) ^ k * v' r = y' := hy'
          have h2 : (2 : ℝ) ^ k * mat U' r jJ = y := by rw [hmat]; exact hy
          exact_mod_cast h1.symm.trans h2
        rw [this] at hyo; exact (Int.not_odd_iff_even.2 hye) hyo
      · refine ⟨?_, by simpa using hr4⟩
        obtain ⟨_, y', hy', hyo⟩ := Finset.mem_filter.1 hr
        rw [hv'eq r hr4] at hy'
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, y', hy', hyo⟩
    have hT : ({a, b, c, d} : Finset (Fin n)) ⊆ S := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      exact hsub x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
    have hTcard : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        simp only [ne_eq, Fin.ext_iff]; simp only [Fin.lt_def] at hab hbc hcd; omega
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
      rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
        Finset.card_insert_of_notMem (by simp [h4, h5]),
        Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
    have hcard' : (oddSet v' k).card + 4 ≤ S.card := by
      have := Finset.card_le_card hodd'
      rw [Finset.card_sdiff_of_subset hT, hTcard] at this
      omega
    -- the measure decreases
    have hex' := intAt_exists v' (col_mem U' jJ)
    have hk'le : Nat.find hex' ≤ k := Nat.find_min' hex' hint'
    have hmeas : measure U' jJ < N := by
      rw [← hN]
      show Nat.find hex' * (n + 1) + (oddSet v' (Nat.find hex')).card <
        Nat.find hex * (n + 1) + (oddSet v (Nat.find hex)).card
      rw [← hkdef]
      rcases Nat.eq_or_lt_of_le hk'le with heq | hlt
      · rw [heq, ← hSdef]; omega
      · have h1 := oddSet_card_le v' (Nat.find hex')
        have h2 : Nat.find hex' * (n + 1) + (n + 1) ≤ k * (n + 1) := by
          have := Nat.mul_le_mul_right (n + 1) hlt; rw [Nat.succ_mul] at this; exact this
        omega
    obtain ⟨w₂, hw₂⟩ := ih _ hmeas U' rfl hfix'
    refine ⟨w₂ * FreeMonoid.ofList (Gen.k a b c d hab hbc hcd :: lsign.map Gen.neg), ?_⟩
    rw [map_mul, mul_assoc]
    exact hw₂

/-- Lemma 3.4, iterated over the columns. -/
theorem reduce (J : ℕ) (hJ : J ≤ n) :
    ∀ U : O_ZHalf n, FixCols (mat U) J → ∃ w : Word (Gen n), FreeMonoid.lift (sem n) w * U = 1 := by
  induction J with
  | zero => intro U h; exact ⟨1, by rw [map_one, one_mul]; exact eq_one_of_fixCols_zero U h⟩
  | succ J ih =>
    intro U h
    obtain ⟨w₁, hw₁⟩ := colStep J (by omega) _ U rfl h
    obtain ⟨w₂, hw₂⟩ := ih (by omega) _ hw₁
    exact ⟨w₂ * w₁, by rw [map_mul, mul_assoc]; exact hw₂⟩

/-- Theorem 3.5: every element of `Oₙ(ℤ[1/2])` is a product of generators. -/
theorem generation : Function.Surjective (FreeMonoid.lift (sem n)) := by
  intro U
  obtain ⟨w, hw⟩ := reduce n le_rfl U⁻¹ (fun i hi => absurd i.2 (by omega))
  exact ⟨w, mul_inv_eq_one.1 hw⟩

end

end QCert.LiRossSelinger
