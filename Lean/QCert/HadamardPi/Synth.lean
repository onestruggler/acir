/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Algorithm 1: syllables, Theorem 4.10, normal words and generation

See `QCert.HadamardPi.Normal` for the levels.  Here: the syllable of a state
(Definition A.1), the proof that it strictly decreases the level
(Theorem 4.10), the normal words, and generation (Theorem 4.8): every
element of `Oₙ(ℤ[1/√2])` is the value of a word.
-/
import QCert.HadamardPi.Normal

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

/-- The partners of an odd entry `i`: the odd entries after it with the
same residue mod 2 (Line 6 of Algorithm 1). -/
noncomputable def partners (v : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  open Classical in univ.filter fun i' => i < i' ∧ SameOdd (num v i) (num v i')

theorem mem_partners {v : Fin n → ℝ} {i i' : Fin n} :
    i' ∈ partners v i ↔ i < i' ∧ SameOdd (num v i) (num v i') := by
  classical
  simp [partners]

/-- The nonzero entries. -/
noncomputable def support (v : Fin n → ℝ) : Finset (Fin n) :=
  open Classical in univ.filter fun i => v i ≠ 0

theorem mem_support {v : Fin n → ℝ} {i : Fin n} : i ∈ support v ↔ v i ≠ 0 := by
  classical
  simp [support]

/-- The syllable at a positive exponent, from the odd entries `O` and the
partners `P` (Lines 5–8 of Algorithm 1). -/
noncomputable def sylPos (j : Fin n) (O : Finset (Fin n)) (P : Fin n → Finset (Fin n)) :
    Word (Gen n) :=
  if h1 : O.Nonempty then
    if h2 : (P (O.min' h1)).Nonempty then
      if hz2 : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.2⟩ : Fin n) < (P (O.min' h1)).min' h2 then
        FreeMonoid.of (Gen.H _ _ hz2) *
          (if hz1 : (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.2⟩ : Fin n) < O.min' h1
            then FreeMonoid.of (Gen.X _ _ hz1) else 1)
      else 1
    else 1
  else 1

/-- The syllable output by one step of Algorithm 1 on the column `v` at
the pivot index `j` (Definition A.1); indices from 0. -/
noncomputable def sylOf (j : Fin n) (v : Fin n → ℝ) : Word (Gen n) :=
  open Classical in
  if lde v = 0 then
    if ha : (support v).Nonempty then
      (if hlt : (support v).min' ha < j then FreeMonoid.of (Gen.X _ j hlt) else 1) *
        (if v ((support v).min' ha) < 0 then FreeMonoid.of (Gen.Z ((support v).min' ha)) else 1)
    else 1
  else sylPos j (oddSet v) (partners v)

theorem sylOf_eq_sylPos {j : Fin n} {v : Fin n → ℝ} (hk : lde v ≠ 0) :
    sylOf j v = sylPos j (oddSet v) (partners v) := by
  rw [sylOf, if_neg hk]

/-- The syllable of a state (`1` for the identity). -/
noncomputable def syl (M : O n) : Word (Gen n) :=
  if h : 0 < piv M then sylOf (pj M h) (col M (pj M h)) else 1

/-- The syllable at exponent 0, where the column is `±e_a`. -/
theorem sylOf_zero {j : Fin n} {v : Fin n → ℝ} (hk : lde v = 0) {a : Fin n} {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (hva : v = Pi.single a ε) :
    sylOf j v = (if hlt : a < j then FreeMonoid.of (Gen.X a j hlt) else 1) *
      (if ε < 0 then FreeMonoid.of (Gen.Z a) else 1) := by
  classical
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hsupp : support v = {a} := by
    ext i; rw [mem_support, hva, mem_singleton]
    by_cases h : i = a
    · subst h; simp [hε0]
    · simp [h]
  have ha : (support v).Nonempty := by rw [hsupp]; exact singleton_nonempty a
  have hmin : (support v).min' ha = a := by
    have := mem_support.1 ((support v).min'_mem ha)
    by_contra h
    have h' := congrFun hva ((support v).min' ha)
    rw [Pi.single_eq_of_ne h] at h'
    exact this h'
  rw [sylOf, if_pos hk, dif_pos ha]
  generalize hm : (support v).min' ha = a' at *
  subst hmin
  rw [hva, Pi.single_eq_same]

/-- The syllable at a positive exponent. -/
theorem sylOf_pos {j : Fin n} {v : Fin n → ℝ} (hk : lde v ≠ 0) (h1 : (oddSet v).Nonempty)
    (h2 : (partners v ((oddSet v).min' h1)).Nonempty)
    (z : Fin n) (hz : z = ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.2⟩)
    (hz2 : z < (partners v ((oddSet v).min' h1)).min' h2) :
    sylOf j v = FreeMonoid.of (Gen.H z _ hz2) *
      (if hz1 : z < (oddSet v).min' h1 then FreeMonoid.of (Gen.X z _ hz1) else 1) := by
  subst hz
  rw [sylOf, if_neg hk, sylPos, dif_pos h1, dif_pos h2, dif_pos hz2]

/-! ### Partners exist -/

/-- An odd entry has an odd partner of the same class (Lemma 5.13 of Amy
et al.: each class has an even number of odd entries). -/
theorem exists_partner {v : Fin n → ℝ} (hR : InRing v) (hU : IsUnitVec v) (hk : 1 ≤ lde v)
    {i : Fin n} (hi : Odd (num v i).re) : ∃ i', i' ≠ i ∧ SameOdd (num v i) (num v i') := by
  classical
  set A := univ.filter fun i => Odd (num v i).re ∧ Odd (num v i).im
  set B := univ.filter fun i => Odd (num v i).re ∧ ¬Odd (num v i).im
  have hA : Even A.card := even_card_odd_odd_num hR hU
  have hAB : A.card + B.card = (oddSet v).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext i'
      simp only [A, B, mem_union, mem_filter, mem_univ, true_and, mem_oddSet]; tauto
    · rw [disjoint_filter]; intro x _ h1 h2; exact h2.2 h1.2
  have hO : Even (oddSet v).card := even_card_oddSet hR hU hk
  have hB : Even B.card := by
    obtain ⟨a, ha⟩ := hA; obtain ⟨o, ho⟩ := hO; exact ⟨o - a, by omega⟩
  by_cases hc : Odd (num v i).im
  · have hiA : i ∈ A := by simp only [A, mem_filter, mem_univ, true_and]; exact ⟨hi, hc⟩
    have h2 : 1 < A.card := by
      obtain ⟨a, ha⟩ := hA
      have := card_pos.2 ⟨i, hiA⟩; omega
    obtain ⟨i', hi', hne⟩ := exists_mem_ne h2 i
    simp only [A, mem_filter, mem_univ, true_and] at hi'
    exact ⟨i', hne, hi, hi'.1, ⟨fun _ => hi'.2, fun _ => hc⟩⟩
  · have hiB : i ∈ B := by simp only [B, mem_filter, mem_univ, true_and]; exact ⟨hi, hc⟩
    have h2 : 1 < B.card := by
      obtain ⟨a, ha⟩ := hB
      have := card_pos.2 ⟨i, hiB⟩; omega
    obtain ⟨i', hi', hne⟩ := exists_mem_ne h2 i
    simp only [B, mem_filter, mem_univ, true_and] at hi'
    exact ⟨i', hne, hi, hi'.1, ⟨fun h => absurd h hc, fun h => absurd h hi'.2⟩⟩

theorem ne_zero_of_odd {v : Fin n → ℝ} (hR : InRing v) {i : Fin n} (h : Odd (num v i).re) :
    v i ≠ 0 := by
  intro h0
  have := toReal_num hR i
  rw [h0, mul_zero] at this
  have : num v i = 0 := toReal_injective (by rw [this, map_zero])
  rw [this] at h
  simp at h

theorem card_oddSet_xv {v : Fin n → ℝ} (hR : InRing v) (p q : Fin n) :
    (oddSet (xv p q v)).card = (oddSet v).card := by
  have : oddSet (xv p q v) = (oddSet v).map (Equiv.swap p q).toEmbedding := by
    ext i
    simp only [mem_map_equiv, mem_oddSet, num_xv p q hR, Equiv.symm_swap]
  rw [this, card_map]

/-! ### Theorem 4.10 -/

/-- Theorem 4.10 (correctness of Algorithm 1): every syllable strictly
decreases the level. -/
theorem lev_syl_lt {M : O n} (hM : M ≠ 1) :
    lev (FreeMonoid.lift (sem n) (syl M) * M) < lev M := by
  classical
  have hp : 0 < piv M := Nat.pos_of_ne_zero fun h => hM (piv_eq_zero_iff.1 h)
  set j := pj M hp with hj
  set v := col M j with hv
  have hR : InRing v := col_inRing M j
  have hU : IsUnitVec v := col_unit M j
  have hnf : ¬Fixed M j := not_fixed_pj hp
  have hjlt : (j : ℕ) < piv M := by simp only [hj, pj]; omega
  have hlow : ∀ i, v i ≠ 0 → (i : ℕ) < piv M := fun i hi => by
    by_contra h
    exact hi (col_eq_zero_of_piv_le hjlt (by omega))
  have hsyl : syl M = sylOf j v := by rw [syl, dif_pos hp]
  rw [hsyl]
  by_cases hk : lde v = 0
  · -- a signed basis vector `±e_a`, sent to `e_j`
    obtain ⟨a, ε, hε, hva⟩ := eq_single_of_lde_zero hR hU hk
    have ha : (a : ℕ) < piv M := hlow a (by rw [hva]; rcases hε with rfl | rfl <;> simp)
    have haj : a ≤ j := by rw [Fin.le_def]; simp only [hj, pj]; omega
    rw [sylOf_zero hk hε hva]
    apply lev_lt_iff.2; left
    apply piv_lt_of_below hp
    · refine Below.mul ?_ ?_
      · split_ifs
        · exact Below.of fun i hi => by
            simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> assumption
        · exact Below.one
      · split_ifs
        · exact Below.of fun i hi => by simp [Gen.idx] at hi; subst hi; exact ha
        · exact Below.one
    · rw [← hj, wv_mul, ← hv, hva]
      have hz : wv (if ε < 0 then FreeMonoid.of (Gen.Z a) else 1) (Pi.single a ε) =
          Pi.single a 1 := by
        rcases hε with rfl | rfl
        · rw [if_neg (by norm_num), wv_one]
        · rw [if_pos (by norm_num), wv_of]
          funext i; simp only [gv, zv]
          split_ifs with h
          · subst h; simp
          · simp [h]
      rw [hz]
      split_ifs with hlt
      · rw [wv_of]
        funext i; simp only [gv, xv]
        split_ifs with h1 h2
        · subst h1; simp [hlt.ne']
        · subst h2; simp
        · simp [Pi.single_apply, h1, h2]
      · have : a = j := le_antisymm haj (not_lt.1 hlt)
        subst this
        rcases hε with rfl | rfl
        · exact absurd (by rw [Fixed, ← hv, hva]) hnf
        · simp
  · -- a positive exponent: `H_[0,i₂]` after moving `i₁` to `0`
    have hk1 : 1 ≤ lde v := Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨i0, hi0⟩ := exists_odd_num hR hk1
    have h1 : (oddSet v).Nonempty := ⟨i0, mem_oddSet.2 hi0⟩
    set i1 := (oddSet v).min' h1 with hi1
    have hi1odd : Odd (num v i1).re := mem_oddSet.1 ((oddSet v).min'_mem h1)
    obtain ⟨i', hi'ne, hi'⟩ := exists_partner hR hU hk1 hi1odd
    have hi'1 : i1 < i' := lt_of_le_of_ne ((oddSet v).min'_le _ (mem_oddSet.2 hi'.2.1))
      (Ne.symm hi'ne)
    have h2 : (partners v i1).Nonempty := ⟨i', mem_partners.2 ⟨hi'1, hi'⟩⟩
    set i2 := (partners v i1).min' h2 with hi2
    have hi2m := mem_partners.1 ((partners v i1).min'_mem h2)
    set z : Fin n := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.2⟩ with hz
    have hz1le : z ≤ i1 := Fin.le_def.2 (Nat.zero_le _)
    have hz2 : z < i2 := lt_of_le_of_lt hz1le hi2m.1
    rw [sylOf_pos hk h1 h2 z hz hz2]
    have hi1p : (i1 : ℕ) < piv M := hlow i1 (ne_zero_of_odd hR hi1odd)
    have hi2p : (i2 : ℕ) < piv M := hlow i2 (ne_zero_of_odd hR hi2m.2.2.1)
    have hzp : (z : ℕ) < piv M := lt_of_le_of_lt (Fin.le_def.1 hz1le) hi1p
    have hbelow : Below (piv M) (FreeMonoid.of (Gen.H z i2 hz2) *
        (if hz1 : z < i1 then FreeMonoid.of (Gen.X z i1 hz1) else 1)) := by
      refine Below.mul (Below.of fun i hi => ?_) ?_
      · simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> assumption
      · split_ifs
        · exact Below.of fun i hi => by
            simp [Gen.idx] at hi; rcases hi with rfl | rfl <;> assumption
        · exact Below.one
    -- the column before the Hadamard
    set w := wv (if hz1 : z < i1 then FreeMonoid.of (Gen.X z i1 hz1) else 1) v with hw
    have hwR : InRing w := by
      simp only [hw]; split_ifs
      · rw [wv_of]; exact inRing_xv _ _ hR
      · rw [wv_one]; exact hR
    have hwl : lde w = lde v := by
      simp only [hw]; split_ifs
      · rw [wv_of]; exact lde_xv _ _ hR
      · rw [wv_one]
    have hwc : (oddSet w).card = (oddSet v).card := by
      simp only [hw]; split_ifs
      · rw [wv_of]; exact card_oddSet_xv hR _ _
      · rw [wv_one]
    have hwz : num w z = num v i1 := by
      simp only [hw]; split_ifs with h
      · rw [wv_of]; simp only [gv]; rw [num_xv _ _ hR, Equiv.swap_apply_left]
      · rw [wv_one]; rw [le_antisymm hz1le (not_lt.1 h)]
    have hw2 : num w i2 = num v i2 := by
      simp only [hw]; split_ifs with h
      · rw [wv_of]; simp only [gv]
        rw [num_xv _ _ hR, Equiv.swap_apply_of_ne_of_ne (ne_of_gt hz2) (ne_of_gt hi2m.1)]
      · rw [wv_one]
    have hpair := pair_reduce hwR (ne_of_lt hz2)
      (by rw [hwz, hw2]; exact hi2m.2)
    apply lev_lt_iff.2
    rcases lt_or_eq_of_le (piv_le_of_below hbelow) with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      rw [pcol_of_piv_eq heq hp, pcol_eq hp, ← hj, ← hv, wv_mul, wv_of, ← hw]
      simp only [gv]
      apply kl_lt_iff.2
      rcases lt_or_eq_of_le hpair.2.1 with hl | hl
      · left; rw [← hwl]; exact hl
      · right
        refine ⟨by rw [hl, hwl], ?_⟩
        have := hpair.2.2 hl
        rw [hl, hwl, if_neg hk, if_neg hk]
        omega

/-! ### Normal words and generation -/

/-- The normal word of a state: its syllables, read until the identity,
the first syllable on the right. -/
noncomputable def nw : O n → Word (Gen n) :=
  (InvImage.wf lev wellFounded_lt).fix fun M ih =>
    open Classical in
    if h : M = 1 then 1 else ih (FreeMonoid.lift (sem n) (syl M) * M) (lev_syl_lt h) * syl M

theorem nw_eq (M : O n) : nw M = open Classical in
    if M = 1 then 1 else nw (FreeMonoid.lift (sem n) (syl M) * M) * syl M := by
  rw [nw, WellFounded.fix_eq]
  split_ifs <;> rfl

theorem nw_one : nw (1 : O n) = 1 := by rw [nw_eq, if_pos rfl]

theorem nw_of_ne {M : O n} (h : M ≠ 1) :
    nw M = nw (FreeMonoid.lift (sem n) (syl M) * M) * syl M := by
  rw [nw_eq, if_neg h]

/-- The normal word reduces its state to the identity. -/
theorem nw_reduces (M : O n) : FreeMonoid.lift (sem n) (nw M) * M = 1 := by
  induction M using (InvImage.wf lev wellFounded_lt).induction with
  | _ M ih =>
    by_cases h : M = 1
    · subst h; rw [nw_one, map_one, one_mul]
    · rw [nw_of_ne h, map_mul, mul_assoc]
      exact ih _ (lev_syl_lt h)

/-- Generation (Theorem 4.8): every element of `Oₙ(ℤ[1/√2])` is the value of
a word over `𝒢ₙ`. -/
theorem lift_sem_surjective : Function.Surjective (FreeMonoid.lift (sem n)) := by
  intro M
  refine ⟨nw M⁻¹, ?_⟩
  have := nw_reduces M⁻¹
  rw [mul_eq_one_iff_eq_inv, inv_inv] at this
  exact this

end QCert.HadamardPi
