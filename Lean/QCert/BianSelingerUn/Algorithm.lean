/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the exact synthesis algorithm

Algorithm 2.14 and Theorem 2.16.  A state is an element `M` of
`Uₙ(ℤ[1/2, i])`; its *pivot column* is the rightmost column where `M`
differs from the identity, and its *level* (Definition 2.15) is
`(p, k, m)`: the index of the pivot column, its least denominator exponent,
and the number of odd entries of its numerator (`(0, 0, 0)` for `M = I`),
ordered lexicographically.  The *syllable* of a state (step 3 of the
algorithm) is

* for `k = 0`: `X_[c,p] i_[c]^e` (or `i_[p]^e` if `c = p`), where the pivot
  column is `i^{-e} e_c` (Corollary 2.8);
* for `k > 0`: `K†_[j,ℓ] i_[ℓ]^q` with `K† = K⁷` (as in the normal words of
  §3.2), `j < ℓ` the first two odd entries and `wⱼ ≡ i^q w_ℓ (mod γ²)`
  (Lemma 2.10, row operation).

Applying the syllable lowers the level (Theorem 2.16); the normal word of a
state is the concatenation of its syllables down to `I`, which reduces the
state to the identity.
-/
import QCert.BianSelingerUn.Gaussian
import QCert.BianSelingerUn.Soundness

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

/-! ### States and columns -/

/-- The states: elements of `Uₙ(ℤ[1/2, i])`. -/
abbrev St (n : ℕ) := ↥(U_ZHalfI n)

/-- The matrix of a state. -/
def sm (s : St n) : Matrix (Fin n) (Fin n) ℂ :=
  ((s : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

@[simp] theorem sm_mul (s t : St n) : sm (s * t) = sm s * sm t := rfl
@[simp] theorem sm_one : sm (1 : St n) = 1 := rfl

theorem St.ext {s t : St n} (h : sm s = sm t) : s = t := Subtype.ext (Subtype.ext h)

@[simp] theorem sm_lift (w : Word (Gen n)) : sm (FreeMonoid.lift (sem n) w) = matOf w :=
  coe_lift_sem w

@[simp] theorem sm_sem (x : Gen n) : sm (sem n x) = mat x := rfl

/-- Column `q` of a state. -/
def col (s : St n) (q : Fin n) : Fin n → ℂ := fun j => sm s j q

/-- The standard basis vector `e_q`. -/
def ev (q : Fin n) : Fin n → ℂ := fun j => if j = q then 1 else 0

theorem col_mem (s : St n) (q j : Fin n) : col s q j ∈ ZHalfI := s.2 j q

theorem col_mul (s t : St n) (q : Fin n) : col (s * t) q = sm s *ᵥ col t q := by
  funext j; simp [col, mul_apply, mulVec, dotProduct]

theorem col_one (q : Fin n) : col 1 q = ev q := by
  funext j; simp [col, ev, one_apply]

theorem star_mul_mat (s : St n) : star (sm s) * sm s = 1 :=
  Matrix.UnitaryGroup.star_mul_self _

/-- A column of a state is a unit vector. -/
theorem col_unit (s : St n) (q : Fin n) : ∑ j, star (col s q j) * col s q j = 1 := by
  have := congrFun (congrFun (star_mul_mat s) q) q
  simpa [mul_apply, col] using this

/-- Two columns of a state are orthogonal. -/
theorem col_orth (s : St n) {p q : Fin n} (h : p ≠ q) :
    ∑ j, star (col s q j) * col s p j = 0 := by
  have := congrFun (congrFun (star_mul_mat s) q) p
  simpa [mul_apply, col, one_apply, Ne.symm h] using this

theorem hasNum_exists (s : St n) (q : Fin n) : ∃ k w, HasNum (col s q) k w :=
  exists_hasNum (col_mem s q)

theorem eq_one_iff (s : St n) : s = 1 ↔ ∀ q, col s q = ev q := by
  constructor
  · rintro rfl q; exact col_one q
  · intro h
    apply St.ext
    ext j q
    have := congrFun (h q) j
    simpa [col, ev, one_apply] using this

/-! ### The pivot column -/

/-- `p` is the pivot column of `s`: the rightmost column where `s` differs
from the identity. -/
def IsPivot (s : St n) (p : Fin n) : Prop := col s p ≠ ev p ∧ ∀ q, p < q → col s q = ev q

theorem IsPivot.unique {s : St n} {p p' : Fin n} (h : IsPivot s p) (h' : IsPivot s p') :
    p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd (h.2 p' hlt) h'.1
  · exact heq
  · exact absurd (h'.2 p hgt) h.1

theorem exists_pivot {s : St n} (hs : s ≠ 1) : ∃ p, IsPivot s p := by
  classical
  rw [Ne, eq_one_iff] at hs
  push Not at hs
  let S := Finset.univ.filter fun q => col s q ≠ ev q
  have hne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hs; exact ⟨q, by simp [S, hq]⟩
  refine ⟨S.max' hne, ?_, fun q hq => ?_⟩
  · have := S.max'_mem hne; simpa [S] using this
  · by_contra hq'
    have : q ∈ S := by simp [S, hq']
    exact absurd (S.le_max' q this) (not_le.2 hq)

theorem IsPivot.ne_one {s : St n} {p : Fin n} (h : IsPivot s p) : s ≠ 1 := by
  rintro rfl; exact h.1 (col_one p)

/-- Below a pivot column the entries vanish: the later columns are basis
vectors, orthogonal to it. -/
theorem IsPivot.entry_zero {s : St n} {p : Fin n} (h : IsPivot s p) {a : Fin n} (ha : p < a) :
    col s p a = 0 := by
  have := col_orth s (ne_of_lt ha)
  rw [h.2 a ha] at this
  simpa [ev] using this

/-! ### Numerators, profiles and levels -/

open Classical in
/-- The numerator of a vector at its least denominator exponent. -/
def num (v : Fin n → ℂ) : Fin n → GaussianInt :=
  if h : ∃ w, HasNum v (lde v) w then h.choose else 0

theorem num_spec {v : Fin n → ℂ} (h : ∃ k w, HasNum v k w) : HasNum v (lde v) (num v) := by
  have h' := lde_spec h
  rw [num, dif_pos h']; exact h'.choose_spec

theorem num_eq {v : Fin n → ℂ} {w : Fin n → GaussianInt} (h : HasNum v (lde v) w) :
    num v = w :=
  (num_spec ⟨_, w, h⟩).unique h

/-- The odd entries of a numerator. -/
def oddSet (w : Fin n → GaussianInt) : Finset (Fin n) := Finset.univ.filter fun j => GOdd (w j)

@[simp] theorem mem_oddSet {w : Fin n → GaussianInt} {j : Fin n} : j ∈ oddSet w ↔ GOdd (w j) := by
  simp [oddSet]

/-- The profile of a column: its least denominator exponent and the number
of odd entries of its numerator. -/
def prof (v : Fin n → ℂ) : ℕ ×ₗ ℕ := toLex (lde v, (oddSet (num v)).card)

theorem prof_eq {v : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum v k w)
    (hk : lde v = k) : prof v = toLex (k, (oddSet w).card) := by
  subst hk; rw [prof, num_eq h]

open Classical in
/-- The level of a state (Definition 2.15). -/
def level (s : St n) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  if h : ∃ p, IsPivot s p then toLex ((h.choose : ℕ), prof (col s h.choose))
  else toLex (0, toLex (0, 0))

theorem level_eq {s : St n} {p : Fin n} (h : IsPivot s p) :
    level s = toLex ((p : ℕ), prof (col s p)) := by
  have h' : ∃ p, IsPivot s p := ⟨p, h⟩
  rw [level, dif_pos h', h'.choose_spec.unique h]

theorem level_one : level (1 : St n) = toLex (0, toLex (0, 0)) := by
  rw [level, dif_neg]
  rintro ⟨p, hp⟩; exact hp.ne_one rfl

/-- Every column of a state has an odd numerator entry. -/
theorem card_oddSet_pos (s : St n) (q : Fin n) : 0 < (oddSet (num (col s q))).card := by
  have hspec := num_spec (hasNum_exists s q)
  rw [Finset.card_pos]
  rcases Nat.eq_zero_or_pos (lde (col s q)) with h0 | hpos
  · rw [h0] at hspec
    have hsum := sum_norm_eq (col_unit s q) hspec
    rw [pow_zero] at hsum
    obtain ⟨c, hc, -⟩ := unit_of_sum_norm_one hsum
    refine ⟨c, mem_oddSet.2 ?_⟩
    have := norm_emod_two (num (col s q) c)
    rw [hc] at this
    unfold GOdd; omega
  · obtain ⟨j, hj⟩ := exists_odd hspec hpos
    exact ⟨j, mem_oddSet.2 hj⟩

theorem prof_pos (s : St n) (q : Fin n) : toLex (0, 0) < prof (col s q) := by
  rw [prof, Prod.Lex.toLex_lt_toLex]
  rcases Nat.eq_zero_or_pos (lde (col s q)) with h0 | hpos
  · right; exact ⟨h0.symm, card_oddSet_pos s q⟩
  · left; exact hpos

/-- A state agreeing with the identity beyond column `p`, whose column `p` is
`e_p` or has a smaller profile than the pivot column of `s`, has a smaller
level. -/
theorem level_lt_of_cols {s t : St n} {p : Fin n} (hs : IsPivot s p)
    (ht : ∀ q, p < q → col t q = ev q)
    (hcol : col t p = ev p ∨ prof (col t p) < prof (col s p)) : level t < level s := by
  rw [level_eq hs]
  by_cases h1 : t = 1
  · subst h1
    rw [level_one, Prod.Lex.toLex_lt_toLex]
    rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | hpos
    · right; exact ⟨h0.symm, prof_pos s p⟩
    · left; exact hpos
  obtain ⟨p', hp'⟩ := exists_pivot h1
  rw [level_eq hp', Prod.Lex.toLex_lt_toLex]
  rcases lt_trichotomy p' p with hlt | rfl | hgt
  · left; exact hlt
  · right
    refine ⟨rfl, ?_⟩
    rcases hcol with h | h
    · exact absurd h hp'.1
    · exact h
  · exact absurd (ht p' hgt) hp'.1

theorem level_le_of_cols {s t : St n} {p : Fin n} (hs : IsPivot s p)
    (ht : ∀ q, p < q → col t q = ev q)
    (hcol : col t p = ev p ∨ prof (col t p) ≤ prof (col s p)) : level t ≤ level s := by
  rcases hcol with h | h
  · exact (level_lt_of_cols hs ht (Or.inl h)).le
  rcases h.lt_or_eq with h | h
  · exact (level_lt_of_cols hs ht (Or.inr h)).le
  by_cases hp : col t p = ev p
  · exact (level_lt_of_cols hs ht (Or.inl hp)).le
  rw [level_eq hs, level_eq (s := t) ⟨hp, ht⟩, h]

end

end QCert.BianSelingerUn
