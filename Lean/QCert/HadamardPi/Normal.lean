/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Algorithm 1: levels, syllables and normal words

The level of a state (Definition 4.9) is the triple `(j, k, l)`: `j` the
largest (1-based) index of a column different from the basis vector, `k`
the least denominator exponent of that column (the *pivot column*), and
`l` the number of odd numerators of the column at exponent `k` (`0` when
`k = 0`).  With 0-based indices, `j = piv M` is one more than the index of
the pivot column, and `0` for the identity.  Levels are ordered
lexicographically.

The syllable of a state (Definition A.1; the words output by one step of
Algorithm 1) at a positive exponent is `H_[0,i₂]` if the first odd entry
`i₁` is `0`, and `H_[0,i₂] X_[0,i₁]` otherwise, `i₂` the next odd entry
with the same residue mod 2 (the paper's `1` is our `0`); at exponent `0`
the pivot column is `±e_a` and the syllable is `(-1)_[a]` (if `a` is the
pivot index) or `X_[a,j] (-1)_[a]^τ`.  Each syllable strictly decreases the
level (Theorem 4.10), so the syllables of a state, read until the identity,
give its normal word `nw M`, with `⟦nw M⟧ M = I`.  Hence every element of
`Oₙ(ℤ[1/√2])` is the value of a word (generation, Theorem 4.8).
-/
import QCert.HadamardPi.Actions
import QCert.Synthesis

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

/-! ### Words acting on columns -/

/-- A word acting on a column. -/
noncomputable def wv (w : Word (Gen n)) (x : Fin n → ℝ) : Fin n → ℝ := wordMat invSqrt2 w *ᵥ x

@[simp] theorem wv_one (x : Fin n → ℝ) : wv 1 x = x := by simp [wv]

theorem wv_mul (w w' : Word (Gen n)) (x : Fin n → ℝ) : wv (w * w') x = wv w (wv w' x) := by
  simp [wv, mulVec_mulVec]

@[simp] theorem wv_of (g : Gen n) (x : Fin n → ℝ) : wv (FreeMonoid.of g) x = gv g x := by
  simp [wv, wordMat, genMat_mulVec]

theorem col_lift_mul' (w : Word (Gen n)) (M : O n) (j : Fin n) :
    col (FreeMonoid.lift (sem n) w * M) j = wv w (col M j) := col_lift_mul w M j

/-- The indices a generator acts on. -/
def Gen.idx : Gen n → Finset (Fin n)
  | .Z p => {p}
  | .X p q _ => {p, q}
  | .H p q _ => {p, q}

/-- A generator fixes the basis vectors away from its indices. -/
theorem gv_single {g : Gen n} {j : Fin n} (h : j ∉ g.idx) :
    gv g (Pi.single j 1) = Pi.single j 1 := by
  cases g with
  | Z p =>
    simp only [Gen.idx, mem_singleton] at h
    funext i; simp only [gv, zv]
    split_ifs with hi
    · subst hi; simp [Pi.single_apply, h]
    · rfl
  | X p q _ =>
    simp only [Gen.idx, mem_insert, mem_singleton, not_or] at h
    funext i; simp only [gv, xv]
    split_ifs with h1 h2
    · subst h1; simp [Pi.single_apply, Ne.symm h.1, Ne.symm h.2]
    · subst h2; simp [Pi.single_apply, Ne.symm h.1, Ne.symm h.2]
    · rfl
  | H p q _ =>
    simp only [Gen.idx, mem_insert, mem_singleton, not_or] at h
    funext i; simp only [gv, hv]
    split_ifs with h1 h2
    · subst h1; simp [Pi.single_apply, Ne.symm h.1, Ne.symm h.2]
    · subst h2; simp [Pi.single_apply, Ne.symm h.1, Ne.symm h.2]
    · rfl

/-- Every letter of `w` acts on indices below `J`. -/
def Below (J : ℕ) (w : Word (Gen n)) : Prop := ∀ g ∈ w.toList, ∀ i ∈ g.idx, (i : ℕ) < J

theorem Below.mul {J : ℕ} {w w' : Word (Gen n)} (h : Below J w) (h' : Below J w') :
    Below J (w * w') := by
  intro g hg; rw [FreeMonoid.toList_mul, List.mem_append] at hg
  rcases hg with hg | hg
  · exact h g hg
  · exact h' g hg

theorem Below.of {J : ℕ} {g : Gen n} (h : ∀ i ∈ g.idx, (i : ℕ) < J) : Below J (FreeMonoid.of g) := by
  intro g' hg'; simp at hg'; subst hg'; exact h

theorem Below.one {J : ℕ} : Below J (1 : Word (Gen n)) := by intro g hg; simp at hg

theorem wv_single_of_below {J : ℕ} {w : Word (Gen n)} (hw : Below J w) {j : Fin n}
    (hj : J ≤ j) : wv w (Pi.single j 1) = Pi.single j 1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [wv_mul, ih (fun g' hg' => hw g' (by simp [hg'])), wv_of]
    apply gv_single
    intro hjg
    have := hw g (by simp) j hjg
    omega

/-! ### Pivots and levels -/

/-- One more than the index of the last column different from the basis
vector (the first component of the level); `0` for the identity. -/
noncomputable def piv (M : O n) : ℕ :=
  open Classical in (univ.filter fun j => ¬Fixed M j).sup fun j => (j : ℕ) + 1

theorem fixed_of_piv_le {M : O n} {j : Fin n} (h : piv M ≤ j) : Fixed M j := by
  classical
  by_contra hf
  have : (j : ℕ) + 1 ≤ piv M :=
    Finset.le_sup (f := fun j : Fin n => (j : ℕ) + 1) (by simp [hf])
  omega

theorem piv_le {M : O n} {J : ℕ} (h : ∀ j : Fin n, J ≤ j → Fixed M j) : piv M ≤ J := by
  classical
  apply Finset.sup_le
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj
  by_contra hlt
  exact hj (h j (by omega))

theorem piv_le_n (M : O n) : piv M ≤ n := piv_le fun j hj => absurd j.2 (by omega)

theorem piv_eq_zero_iff {M : O n} : piv M = 0 ↔ M = 1 := by
  constructor
  · intro h; exact eq_one_of_fixed fun j => fixed_of_piv_le (by omega)
  · rintro rfl
    apply Nat.eq_zero_of_le_zero
    apply piv_le
    intro j _ ; funext i; simp [col, one_apply, Pi.single_apply, eq_comm]

/-- The index of the pivot column. -/
noncomputable def pj (M : O n) (h : 0 < piv M) : Fin n := ⟨piv M - 1, by have := piv_le_n M; omega⟩

theorem not_fixed_pj {M : O n} (h : 0 < piv M) : ¬Fixed M (pj M h) := by
  classical
  intro hf
  have : piv M ≤ piv M - 1 := piv_le fun j hj => by
    by_cases hjj : (j : ℕ) = piv M - 1
    · have : j = pj M h := Fin.ext hjj
      rw [this]; exact hf
    · exact fixed_of_piv_le (by omega)
  omega

/-- Below the pivot, a column vanishes at the indices of fixed columns. -/
theorem col_eq_zero_of_piv_le {M : O n} {j i : Fin n} (hj : (j : ℕ) < piv M) (hi : piv M ≤ i) :
    col M j i = 0 :=
  mat_eq_zero_of_fixed (fixed_of_piv_le hi) (by intro h; subst h; omega)

/-- The pivot column (`0` for the identity). -/
noncomputable def pcol (M : O n) : Fin n → ℝ :=
  if h : 0 < piv M then col M (pj M h) else 0

/-- The numerical part `(k, l)` of the level of a column. -/
noncomputable def kl (v : Fin n → ℝ) : ℕ ×ₗ ℕ :=
  toLex (lde v, if lde v = 0 then 0 else (oddSet v).card)

/-- The level of a state (Definition 4.9), ordered lexicographically. -/
noncomputable def lev (M : O n) : ℕ ×ₗ (ℕ ×ₗ ℕ) := toLex (piv M, kl (pcol M))

theorem lev_lt_iff {M M' : O n} :
    lev M' < lev M ↔ piv M' < piv M ∨ piv M' = piv M ∧ kl (pcol M') < kl (pcol M) :=
  Prod.Lex.toLex_lt_toLex

theorem kl_lt_iff {v v' : Fin n → ℝ} : kl v' < kl v ↔ lde v' < lde v ∨ lde v' = lde v ∧
    (if lde v' = 0 then 0 else (oddSet v').card) < (if lde v = 0 then 0 else (oddSet v).card) :=
  Prod.Lex.toLex_lt_toLex

/-- A word acting below the pivot does not move the pivot up, and if it
fixes the pivot column the pivot moves down. -/
theorem piv_le_of_below {M : O n} {w : Word (Gen n)} (hw : Below (piv M) w) :
    piv (FreeMonoid.lift (sem n) w * M) ≤ piv M := by
  apply piv_le
  intro j hj
  show col _ j = _
  rw [col_lift_mul', fixed_of_piv_le hj, wv_single_of_below hw hj]

theorem piv_lt_of_below {M : O n} (h : 0 < piv M) {w : Word (Gen n)} (hw : Below (piv M) w)
    (hfix : wv w (col M (pj M h)) = Pi.single (pj M h) 1) :
    piv (FreeMonoid.lift (sem n) w * M) < piv M := by
  have : piv (FreeMonoid.lift (sem n) w * M) ≤ piv M - 1 := by
    apply piv_le
    intro j hj
    by_cases hjj : (j : ℕ) = piv M - 1
    · have : j = pj M h := Fin.ext hjj
      subst this
      show col _ _ = _
      rw [col_lift_mul', hfix]
    · show col _ j = _
      rw [col_lift_mul', fixed_of_piv_le (by omega), wv_single_of_below hw (by omega)]
  omega

/-- If the pivot stays, the pivot column of `⟦w⟧ M` is `w` applied to it. -/
theorem pcol_of_piv_eq {M : O n} {w : Word (Gen n)}
    (h : piv (FreeMonoid.lift (sem n) w * M) = piv M) (hp : 0 < piv M) :
    pcol (FreeMonoid.lift (sem n) w * M) = wv w (col M (pj M hp)) := by
  have hp' : 0 < piv (FreeMonoid.lift (sem n) w * M) := h ▸ hp
  rw [pcol, dif_pos hp', ← col_lift_mul']
  have : pj _ hp' = pj M hp := Fin.ext (by simp only [pj]; rw [h])
  rw [this]

theorem pcol_eq {M : O n} (hp : 0 < piv M) : pcol M = col M (pj M hp) := by
  rw [pcol, dif_pos hp]

/-! ### Two odd entries of the same class -/

/-- `u` and `w` are odd of the same class. -/
def SameOdd (u w : ℤ√2) : Prop := Odd u.re ∧ Odd w.re ∧ (Odd u.im ↔ Odd w.im)

/-- `H_[p,q]` on two odd numerators of the same class makes both even at
the same exponent: the exponent does not grow, and if it stays, the number
of odd numerators drops by two. -/
theorem pair_reduce {v : Fin n → ℝ} (hR : InRing v) {p q : Fin n} (hpq : p ≠ q)
    (hs : SameOdd (num v p) (num v q)) :
    InRing (hv p q v) ∧ lde (hv p q v) ≤ lde v ∧
      (lde (hv p q v) = lde v → (oddSet (hv p q v)).card + 2 = (oddSet v).card) := by
  classical
  obtain ⟨hp, hq, hc⟩ := hs
  have hre : Even ((num v p).re + (num v q).re) := Odd.add_odd hp hq
  have him : Even ((num v p).im + (num v q).im) := by
    rcases Int.even_or_odd (num v p).im with h | h
    · exact Even.add h (Int.not_odd_iff_even.1 fun h' => Int.not_odd_iff_even.2 h (hc.2 h'))
    · exact Odd.add_odd h (hc.1 h)
  have hre' : Even ((num v p).re + (-num v q).re) := by
    simpa [← sub_eq_add_neg, Int.even_sub] using (Int.even_add.1 hre)
  have him' : Even ((num v p).im + (-num v q).im) := by
    simpa [← sub_eq_add_neg, Int.even_sub] using (Int.even_add.1 him)
  obtain ⟨z1, hz1⟩ := exists_half hre him
  obtain ⟨z2, hz2⟩ := exists_half hre' him'
  set k := lde v
  have hp' := toReal_num hR p
  have hq' := toReal_num hR q
  -- the numerators of the new column at exponent `k`
  set u : Fin n → ℤ√2 := fun i => if i = p then rt2 * z1 else if i = q then rt2 * z2 else num v i
  have hu : ∀ i, toReal (u i) = Real.sqrt 2 ^ k * hv p q v i := by
    intro i
    simp only [u, hv]
    split_ifs with h1 h2
    · exact den_of_two_mul (by rw [← hz1]; exact den_hsum hp' hq')
    · exact den_of_two_mul (by rw [← hz2, ← sub_eq_add_neg]; exact den_hdiff hp' hq')
    · exact toReal_num hR i
  have hring : InRing (hv p q v) := fun i => by
    simp only [hv]
    split_ifs
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.add_mem (hR p) (hR q))
    · exact ZInvSqrt2.mul_mem invSqrt2_mem (ZInvSqrt2.sub_mem (hR p) (hR q))
    · exact hR i
  have hden : DenV (hv p q v) k := fun i => ⟨u i, hu i⟩
  refine ⟨hring, lde_le hden, fun heq => ?_⟩
  have hnum : num (hv p q v) = u := num_eq hring (by rw [heq]; exact hu)
  have : oddSet (hv p q v) = ((oddSet v).erase p).erase q := by
    ext i
    simp only [mem_erase, mem_oddSet, hnum, u]
    by_cases h1 : i = p
    · subst h1; simp [rt2]
    · by_cases h2 : i = q
      · subst h2; simp [h1, rt2]
      · simp [h1, h2]
  rw [this, card_erase_of_mem (mem_erase.2 ⟨Ne.symm hpq, mem_oddSet.2 hq⟩),
    card_erase_of_mem (mem_oddSet.2 hp)]
  have : 2 ≤ (oddSet v).card := by
    have : ({p, q} : Finset (Fin n)) ⊆ oddSet v := by
      intro i hi; simp at hi; rcases hi with rfl | rfl
      · exact mem_oddSet.2 hp
      · exact mem_oddSet.2 hq
    have := card_le_card this
    rwa [card_pair hpq] at this
  omega

end QCert.HadamardPi
